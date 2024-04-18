#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "freertos/event_groups.h"
#include "esp_system.h"
#include "esp_log.h"
#include "nvs_flash.h"
#include "esp_bt.h"
#include "driver/uart.h"
#include "string.h"
#include "driver/gpio.h"

#include "esp_gap_ble_api.h"
#include "esp_gatts_api.h"
#include "esp_bt_defs.h"
#include "esp_bt_main.h"
#include "ble_spp_server_demo.h"

#define GATTS_TABLE_TAG  "GATTS_SPP_DEMO"

#define SPP_PROFILE_NUM             1
#define SPP_PROFILE_APP_IDX         0
#define ESP_SPP_APP_ID              0x56
#define SAMPLE_DEVICE_NAME          "ESP_SPP_SERVER"    //The Device Name Characteristics in GAP
#define SPP_SVC_INST_ID	            0

static const uint8_t spp_adv_data[23] = {
    /* Flags */
    0x02,0x01,0x06,
    /* Complete List of 16-bit Service Class UUIDs */
    0x03,0x03,0xF0,0xAB,
    /* Complete Local Name in advertising */
    0x0F,0x09, 'E', 'S', 'P', '_', 'S', 'P', 'P', '_', 'S', 'E', 'R','V', 'E', 'R'
};

static uint16_t spp_mtu_size = 23;
static uint16_t spp_conn_id = 0xffff;
static esp_gatt_if_t spp_gatts_if = 0xff;
static QueueHandle_t ml41_request_queue = NULL;

static bool enable_data_ntf = false;
static bool is_connected = false;
static esp_bd_addr_t spp_remote_bda = {0x0,};

static uint16_t spp_handle_table[SPP_IDX_NB];

static esp_ble_adv_params_t spp_adv_params = {
    .adv_int_min        = 0x20,
    .adv_int_max        = 0x40,
    .adv_type           = ADV_TYPE_IND,
    .own_addr_type      = BLE_ADDR_TYPE_PUBLIC,
    .channel_map        = ADV_CHNL_ALL,
    .adv_filter_policy  = ADV_FILTER_ALLOW_SCAN_ANY_CON_ANY,
};

struct gatts_profile_inst {
    esp_gatts_cb_t gatts_cb;
    uint16_t gatts_if;
    uint16_t app_id;
    uint16_t conn_id;
    uint16_t service_handle;
    esp_gatt_srvc_id_t service_id;
    uint16_t char_handle;
    esp_bt_uuid_t char_uuid;
    esp_gatt_perm_t perm;
    esp_gatt_char_prop_t property;
    uint16_t descr_handle;
    esp_bt_uuid_t descr_uuid;
};

typedef struct spp_data {
    uint16_t size;
    uint8_t *data;
} spp_data_t;

enum EcuRequestID {
    NoData, // 0x00
    EndSession, // 0x01
    ReadEPROM, // 0x02
    GetAFR, // 0x06
    GetVBat, // 0x07
    GetIntakeAirTemp, // 0x08
    GetCoolantTemp, // 0x09
    EraseErrorCodes, // 0x0A
    GetCOPot, // 0x0C
    GetO2Sensor, // 0x0D
    GetIgnitionTime, // 0x0F
    GetErrorCodes, // 0x11
    GetRPM, // 0x12
    GetTPS, // 0x13
    GetEngineLoad, // 0x14
    GetInjectionTime, // 0x15
    GetACParams, // 0x19
    GetO2Params, // 0x1A
    GetFuelPumpParams, // 0x1B
    GetAdsorberParams, // 0x1C
    EnableInjector, // 0x1D
    EnableAdsorberValve, // 0x1E
    EnableIdleValve, // 0x1F
    EcuRequestMax
};

typedef enum {
    Disconnected,
    Initialization,
    Connected
} ECUConnectionState_t;

#define LED_GPIO 2
#define LED_BLINK_DELAY 200
#define delay(ms) vTaskDelay(ms / portTICK_PERIOD_MS)

void enable_led(void)
{
    gpio_set_level(LED_GPIO, 1);
}

void disable_led(void)
{
    gpio_set_level(LED_GPIO, 0);
}

void blink_led(uint8_t count)
{
    disable_led();

    do {
        delay(LED_BLINK_DELAY);
        enable_led();
        delay(LED_BLINK_DELAY);
        disable_led();
    } while (--count > 0);
}

void configure_led(void)
{
    gpio_reset_pin(LED_GPIO);

    gpio_set_direction(LED_GPIO, GPIO_MODE_OUTPUT);
}
static int ecu_connection_state = Disconnected;

static void gatts_profile_event_handler(esp_gatts_cb_event_t event, esp_gatt_if_t gatts_if, esp_ble_gatts_cb_param_t *param);

/* One gatt-based profile one app_id and one gatts_if, this array will store the gatts_if returned by ESP_GATTS_REG_EVT */
static struct gatts_profile_inst spp_profile_tab[SPP_PROFILE_NUM] = {
    [SPP_PROFILE_APP_IDX] = {
        .gatts_cb = gatts_profile_event_handler,
        .gatts_if = ESP_GATT_IF_NONE,       /* Not get the gatt_if, so initial is ESP_GATT_IF_NONE */
    },
};

/*
 *  SPP PROFILE ATTRIBUTES
 ****************************************************************************************
 */
#define CHAR_DECLARATION_SIZE   (sizeof(uint8_t))
static const uint16_t primary_service_uuid = ESP_GATT_UUID_PRI_SERVICE;
static const uint16_t character_declaration_uuid = ESP_GATT_UUID_CHAR_DECLARE;
static const uint16_t character_client_config_uuid = ESP_GATT_UUID_CHAR_CLIENT_CONFIG;

static const uint8_t char_prop_read_notify = ESP_GATT_CHAR_PROP_BIT_READ|ESP_GATT_CHAR_PROP_BIT_NOTIFY;
static const uint8_t char_prop_read_write = ESP_GATT_CHAR_PROP_BIT_WRITE_NR|ESP_GATT_CHAR_PROP_BIT_READ;

/// SPP Service
static const uint16_t spp_service_uuid = 0xABF0;

///SPP Service - data receive characteristic, read&write without response
static const uint16_t spp_data_receive_uuid = 0xABF1;
static const uint8_t  spp_data_receive_val[20] = { 0x00 };

///SPP Service - data notify characteristic, notify&read
static const uint16_t spp_data_notify_uuid = 0xABF2;
static const uint8_t  spp_data_notify_val[20] = { 0x00 };
static const uint8_t  spp_data_notify_ccc[2] = { 0x00, 0x00 };

///Full HRS Database Description - Used to add attributes into the database
static const esp_gatts_attr_db_t spp_gatt_db[SPP_IDX_NB] =
{
    //SPP -  Service Declaration
    [SPP_IDX_SVC] =
    {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *) &primary_service_uuid, ESP_GATT_PERM_READ,
    sizeof(spp_service_uuid), sizeof(spp_service_uuid), (uint8_t *) &spp_service_uuid}},

    //SPP -  data receive characteristic Declaration
    [SPP_IDX_SPP_DATA_RECV_CHAR] =
    {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *) &character_declaration_uuid, ESP_GATT_PERM_READ,
    CHAR_DECLARATION_SIZE,CHAR_DECLARATION_SIZE, (uint8_t *) &char_prop_read_write}},

    //SPP -  data receive characteristic Value
    [SPP_IDX_SPP_DATA_RECV_VAL] =
    {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *) &spp_data_receive_uuid, ESP_GATT_PERM_READ|ESP_GATT_PERM_WRITE,
    SPP_DATA_MAX_LEN,sizeof(spp_data_receive_val), (uint8_t *) spp_data_receive_val}},

    //SPP -  data notify characteristic Declaration
    [SPP_IDX_SPP_DATA_NOTIFY_CHAR] =
    {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *) &character_declaration_uuid, ESP_GATT_PERM_READ,
    CHAR_DECLARATION_SIZE,CHAR_DECLARATION_SIZE, (uint8_t *) &char_prop_read_notify}},

    //SPP -  data notify characteristic Value
    [SPP_IDX_SPP_DATA_NTY_VAL] =
    {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *) &spp_data_notify_uuid, ESP_GATT_PERM_READ,
    SPP_DATA_MAX_LEN, sizeof(spp_data_notify_val), (uint8_t *) spp_data_notify_val}},

    // //SPP -  data notify characteristic - Client Characteristic Configuration Descriptor
    [SPP_IDX_SPP_DATA_NTF_CFG] =
    {{ESP_GATT_AUTO_RSP}, {ESP_UUID_LEN_16, (uint8_t *)&character_client_config_uuid, ESP_GATT_PERM_READ|ESP_GATT_PERM_WRITE,
    sizeof(uint16_t),sizeof(spp_data_notify_ccc), (uint8_t *)spp_data_notify_ccc}},
};

static uint8_t find_char_and_desr_index(uint16_t handle)
{
    uint8_t error = 0xff;

    for (int i = 0; i < SPP_IDX_NB ; i++) {
        if (handle == spp_handle_table[i])
            return i;
    }

    return error;
}

void send_notification(spp_data_t *spp_message)
{
    if (!enable_data_ntf) {
        ESP_LOGE(GATTS_TABLE_TAG, "%s do not enable data Notify", __func__);

        return;
    }

    esp_ble_gatts_send_indicate(spp_gatts_if, spp_conn_id, spp_handle_table[SPP_IDX_SPP_DATA_NTY_VAL], spp_message->size, spp_message->data, false);
}

void set_connection_state(ECUConnectionState_t newState)
{
    ecu_connection_state = newState;

    // spp_data_t spp_message = {
    //     .data = { 0x01, (uint8_t) newState },
    //     .size = 2
    // };

    // send_notification(&spp_message);
}

static void ml41_connection_task()
{
    spp_data_t *spp_message;

    set_connection_state(Initialization);

    blink_led(10);
    // vTaskDelay(5000 / portTICK_PERIOD_MS);

    set_connection_state(Connected);

    spp_data_t *no_data_notify = malloc(sizeof(spp_data_t)); 

    no_data_notify->data = malloc(5);

    no_data_notify->data[0] = 0x04;
    no_data_notify->data[1] = 0x03;
    no_data_notify->data[2] = 0x00;
    no_data_notify->data[3] = 0x09;
    no_data_notify->data[4] = 0x03;

    no_data_notify->size = 5;

    for(;;) {
        // vTaskDelay(50 / portTICK_PERIOD_MS);

        if (xQueueReceive(ml41_request_queue, &spp_message, 50 / portTICK_PERIOD_MS)) {
            ESP_LOGI(GATTS_TABLE_TAG, "message size: %d message ptr: %p data ptr: %p \r\n", spp_message->size, spp_message, spp_message->data);

            ESP_LOG_BUFFER_HEXDUMP(GATTS_TABLE_TAG, spp_message->data, spp_message->size, ESP_LOG_INFO);

            send_notification(spp_message);

            free(spp_message->data);
            free(spp_message);
        } else {
            send_notification(no_data_notify);
        }

        // if (enable_data_ntf)
        //     esp_ble_gatts_send_indicate(spp_gatts_if, spp_conn_id, spp_handle_table[SPP_IDX_SPP_DATA_NTY_VAL], spp_message->size, spp_message->data, false);
        // else
        //     ESP_LOGE(GATTS_TABLE_TAG, "%s do not enable data Notify", __func__);
    }

    free(no_data_notify->data);
    free(no_data_notify);

    vTaskDelete(NULL);
}

static void gap_event_handler(esp_gap_ble_cb_event_t event, esp_ble_gap_cb_param_t *param)
{
    esp_err_t err;

    ESP_LOGE(GATTS_TABLE_TAG, "GAP_EVT, event %d", event);

    switch (event) {
        case ESP_GAP_BLE_ADV_DATA_RAW_SET_COMPLETE_EVT:
            esp_ble_gap_start_advertising(&spp_adv_params);
            break;
        case ESP_GAP_BLE_ADV_START_COMPLETE_EVT:
            //advertising start complete event to indicate advertising start successfully or failed
            if ((err = param->adv_start_cmpl.status) != ESP_BT_STATUS_SUCCESS) {
                ESP_LOGE(GATTS_TABLE_TAG, "Advertising start failed: %s", esp_err_to_name(err));
            }
            break;
        default:
            break;
    }
}

static void gatts_profile_event_handler(esp_gatts_cb_event_t event, esp_gatt_if_t gatts_if, esp_ble_gatts_cb_param_t *param)
{
    esp_ble_gatts_cb_param_t *p_data = (esp_ble_gatts_cb_param_t *) param;

    uint8_t res = 0xff;

    switch (event) {
    	case ESP_GATTS_REG_EVT:
        	esp_ble_gap_set_device_name(SAMPLE_DEVICE_NAME);
        	esp_ble_gap_config_adv_data_raw((uint8_t *)spp_adv_data, sizeof(spp_adv_data));
        	esp_ble_gatts_create_attr_tab(spp_gatt_db, gatts_if, SPP_IDX_NB, SPP_SVC_INST_ID);
       	    break;

    	case ESP_GATTS_READ_EVT:
            res = find_char_and_desr_index(p_data->read.handle);
            ESP_LOGI(GATTS_TABLE_TAG, "ESP_GATTS_READ_EVT : handle = %d", res);
          	break;

    	case ESP_GATTS_WRITE_EVT: {
            if (p_data->write.is_prep == true)
                break;

    	    res = find_char_and_desr_index(p_data->write.handle);

            ESP_LOGI(GATTS_TABLE_TAG, "ESP_GATTS_WRITE_EVT : handle = %d", res);

            if (res == SPP_IDX_SPP_DATA_NTF_CFG) {
                if ((p_data->write.len == 2) && (p_data->write.value[1] == 0x00))
                    enable_data_ntf = p_data->write.value[0] == 0x01;
            } else if (res == SPP_IDX_SPP_DATA_RECV_VAL) {
                if (p_data->write.len > 1) {
                    spp_data_t *spp_message = (spp_data_t *) malloc(sizeof(spp_data_t));

                    spp_message->size = p_data->write.len;
                    spp_message->data = (uint8_t *) malloc(p_data->write.len);

                    memcpy(spp_message->data, p_data->write.value, p_data->write.len);

                    xQueueSend(ml41_request_queue, &spp_message, 10 / portTICK_PERIOD_MS);
                    break;
                }

                switch (p_data->write.value[0])
                {
                    case 0x01: // start ecu connection
                        xTaskCreate(ml41_connection_task, "ml41_connection_task", 16384, NULL, configMAX_PRIORITIES - 2, NULL);
                        break;
                    case 0x02:
                    default:
                        break;
                }
            }
      	 	break;
    	}

    	case ESP_GATTS_EXEC_WRITE_EVT:
    	    ESP_LOGI(GATTS_TABLE_TAG, "ESP_GATTS_EXEC_WRITE_EVT");
    	    break;

    	case ESP_GATTS_MTU_EVT:
    	    spp_mtu_size = p_data->mtu.mtu;
    	    break;

    	case ESP_GATTS_CONF_EVT:
    	    break;

    	case ESP_GATTS_UNREG_EVT:
        	break;

    	case ESP_GATTS_DELETE_EVT:
        	break;

    	case ESP_GATTS_START_EVT:
        	break;

    	case ESP_GATTS_STOP_EVT:
        	break;

    	case ESP_GATTS_CONNECT_EVT:
    	    spp_conn_id = p_data->connect.conn_id;
    	    spp_gatts_if = gatts_if;
    	    is_connected = true;
    	    memcpy(&spp_remote_bda, &p_data->connect.remote_bda, sizeof(esp_bd_addr_t));
        	break;

    	case ESP_GATTS_DISCONNECT_EVT:
    	    is_connected = false;
    	    enable_data_ntf = false;
    	    esp_ble_gap_start_advertising(&spp_adv_params);
    	    break;

    	case ESP_GATTS_OPEN_EVT:
    	    break;

    	case ESP_GATTS_CANCEL_OPEN_EVT:
    	    break;

    	case ESP_GATTS_CLOSE_EVT:
    	    break;

    	case ESP_GATTS_LISTEN_EVT:
    	    break;

    	case ESP_GATTS_CONGEST_EVT:
    	    break;

    	case ESP_GATTS_CREAT_ATTR_TAB_EVT:
    	    ESP_LOGI(GATTS_TABLE_TAG, "The number handle =%x",param->add_attr_tab.num_handle);
    	    if (param->add_attr_tab.status != ESP_GATT_OK) {
    	        ESP_LOGE(GATTS_TABLE_TAG, "Create attribute table failed, error code=0x%x", param->add_attr_tab.status);
    	    } else if (param->add_attr_tab.num_handle != SPP_IDX_NB) {
    	        ESP_LOGE(GATTS_TABLE_TAG, "Create attribute table abnormally, num_handle (%d) doesn't equal to HRS_IDX_NB(%d)", param->add_attr_tab.num_handle, SPP_IDX_NB);
    	    } else {
    	        memcpy(spp_handle_table, param->add_attr_tab.handles, sizeof(spp_handle_table));
    	        esp_ble_gatts_start_service(spp_handle_table[SPP_IDX_SVC]);
    	    }
    	    break;

    	default:
    	    break;
    }
}

static void gatts_event_handler(esp_gatts_cb_event_t event, esp_gatt_if_t gatts_if, esp_ble_gatts_cb_param_t *param)
{
    ESP_LOGI(GATTS_TABLE_TAG, "EVT %d, gatts if %d", event, gatts_if);

    /* If event is register event, store the gatts_if for each profile */
    if (event == ESP_GATTS_REG_EVT) {
        if (param->reg.status == ESP_GATT_OK) {
            spp_profile_tab[SPP_PROFILE_APP_IDX].gatts_if = gatts_if;
        } else {
            ESP_LOGI(GATTS_TABLE_TAG, "Reg app failed, app_id %04x, status %d",param->reg.app_id, param->reg.status);
            return;
        }
    }

    for (int idx = 0; idx < SPP_PROFILE_NUM; idx++) {
        if (gatts_if == ESP_GATT_IF_NONE || /* ESP_GATT_IF_NONE, not specify a certain gatt_if, need to call every profile cb function */
                gatts_if == spp_profile_tab[idx].gatts_if) {
            if (spp_profile_tab[idx].gatts_cb) {
                spp_profile_tab[idx].gatts_cb(event, gatts_if, param);
            }
        }
    }
}

void app_main(void)
{
    configure_led();

    esp_err_t ret;
    esp_bt_controller_config_t bt_cfg = BT_CONTROLLER_INIT_CONFIG_DEFAULT();

    // Initialize NVS
    ret = nvs_flash_init();
    if (ret == ESP_ERR_NVS_NO_FREE_PAGES || ret == ESP_ERR_NVS_NEW_VERSION_FOUND) {
        ESP_ERROR_CHECK(nvs_flash_erase());
        ret = nvs_flash_init();
    }
    ESP_ERROR_CHECK( ret );

    ESP_ERROR_CHECK(esp_bt_controller_mem_release(ESP_BT_MODE_CLASSIC_BT));

    ret = esp_bt_controller_init(&bt_cfg);
    if (ret) {
        ESP_LOGE(GATTS_TABLE_TAG, "%s enable controller failed: %s", __func__, esp_err_to_name(ret));
        return;
    }

    ret = esp_bt_controller_enable(ESP_BT_MODE_BLE);
    if (ret) {
        ESP_LOGE(GATTS_TABLE_TAG, "%s enable controller failed: %s", __func__, esp_err_to_name(ret));
        return;
    }

    ESP_LOGI(GATTS_TABLE_TAG, "%s init bluetooth", __func__);

    esp_bluedroid_config_t bluedroid_cfg = BT_BLUEDROID_INIT_CONFIG_DEFAULT();

    ret = esp_bluedroid_init_with_cfg(&bluedroid_cfg);
    if (ret) {
        ESP_LOGE(GATTS_TABLE_TAG, "%s init bluetooth failed: %s", __func__, esp_err_to_name(ret));
        return;
    }

    ret = esp_bluedroid_enable();
    if (ret) {
        ESP_LOGE(GATTS_TABLE_TAG, "%s enable bluetooth failed: %s", __func__, esp_err_to_name(ret));
        return;
    }

    esp_ble_gatts_register_callback(gatts_event_handler);
    esp_ble_gap_register_callback(gap_event_handler);
    esp_ble_gatts_app_register(ESP_SPP_APP_ID);

    ml41_request_queue = xQueueCreate(32, sizeof(void *));

    return;
}
