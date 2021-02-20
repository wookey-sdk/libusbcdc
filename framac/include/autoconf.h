/*
 *
 * Automatically generated file; DO NOT EDIT.
 * Wookey configuration
 *
 */
#define CONFIG_STD_MALLOC_LIGHT 1
#define CONFIG_USR_LIB_DFU_CFLAGS " -I@PROJFILES@/libs/dfu/api "
#define CONFIG_USR_LIB_USBHID_CFLAGS " -I@PROJFILES@/libs/usbhid/api "
#define CONFIG_USR_DRV_FLASH 1
#define CONFIG_SCHED_MLQ_RR 1
#define CONFIG_CORE_FREQUENCY 168000
#define CONFIG_DFU_TOKEN_PET_NAME "My cat name is Alice!"
#define CONFIG_USR_LIB_AES_DFU_ALGO_ANSSI_MASKED 1
#define CONFIG_USR_LIB_FIRMWARE_FLOP_BOOTINFO_ADDR 0x08108000
#define CONFIG_USR_LIB_AES_FW_ALGO_CRYP_SUPPORT_DMA 1
#define CONFIG_KERNEL_GETCYCLES 1
#define CONFIG_DRIVERS_CFLAGS "-Os"
#define CONFIG_USR_LIB_AES_CFLAGS " -I@PROJFILES@/libs/aes/api "
#define CONFIG_APP_USB_PRIO 0
#define CONFIG_DBGFLAGS_LLVM "-ggdb -Os"
#define CONFIG_FIRMWARE_BUILD_MODE_DEBUG 1
#define CONFIG_USR_LIB_WOOKEY_CFLAGS " -I@PROJFILES@/libs/wookey/api "
#define CONFIG_AUTH_TOKEN_MAX_SC 10
#define CONFIG_USR_LIB_DRBG_USE_HMAC_DRBG 1
#define CONFIG_ADAKERNEL 1
#define CONFIG_USR_DRV_FLASH_CFLAGS " -I@PROJFILES@/drivers/socs/stm32f439/flash/api "
#define CONFIG_USR_DRV_USB_FS 1
#define CONFIG_USR_DRV_ILI9341_CFLAGS " -I@PROJFILES@/drivers/boards/wookey/ili9341/api "
#define CONFIG_USR_LIB_USBCTRL_CFLAGS " -I@PROJFILES@/libs/usbctrl/api "
#define CONFIG_USR_DRV_USBOTGHS_MODE_DEVICE 1
#define CONFIG_USR_DRV_USART 1
#define CONFIG_APP_USB_PERM_MEM_DYNAMIC_MAP 1
#define CONFIG_SIG_TOKEN_PET_PIN 1234
#define CONFIG_USR_LIB_FIDO 1
#define CONFIG_USR_DRV_HASH 1
#define CONFIG_EXT_GP_PRO 1
#define CONFIG_USR_LIB_HOTP 1
#define CONFIG_USR_DRV_USBOTGFS 1
#define CONFIG_EXT_ANT_JAVACARD 1
#define CONFIG_USR_LIB_FIDO_CFLAGS " -I@PROJFILES@/libs/fido/api "
#define CONFIG_USR_LIB_GUI_MODE_FULL 1
#define CONFIG_ARCH "armv7-m"
#define CONFIG_BIN_NAME "$(CONFIG_PROJ_NAME).bin"
#define CONFIG_AUTH_TOKEN_USER_PIN 1234
#define CONFIG_USR_DRV_FLASH_DUAL_BANK 1
#define CONFIG_USR_LIB_FIRMWARE_FLIP_ADDR 0x08020000
#define CONFIG_USR_LIB_CCID_CFLAGS " -I@PROJFILES@/libs/ccid/api "
#define CONFIG_USR_LIB_CTAP_CFLAGS " -I@PROJFILES@/libs/ctap/api "
#define CONFIG_USR_DRV_USBOTGFS_CFLAGS " -I@PROJFILES@/drivers/socs/stm32f439/usbotgfs/api "
#define CONFIG_USR_LIB_U2FAPDU_DEBUG 2
#define CONFIG_USE_SIG_TOKEN_BOOL 1
#define CONFIG_SHM 1
#define CONFIG_USR_DRV_ILI9341 1
#define CONFIG_USR_LIB_GUI_CFLAGS " -I@PROJFILES@/libs/gui/api "
#define CONFIG_APP_USB_PERM_TSK_RNG 1
#define CONFIG_AUTH_TOKEN_PET_PIN 1234
#define CONFIG_STACK_PROT_FLAG 1
#define CONFIG_LIB_OPTIM_CFLAGS "-Os"
#define CONFIG_USR_LIB_AES_FW_ALGO_ANSSI_MASKED 1
#define CONFIG_LOADER_ERASE_ON_SECBREACH 1
#define CONFIG_APP_USB 1
#define CONFIG_USR_LIB_HMAC 1
#define CONFIG_USR_LIB_DES_CFLAGS " -I@PROJFILES@/libs/des/api "
#define CONFIG_USR_LIB_U2FAPDU_CFLAGS " -I@PROJFILES@/libs/u2fapdu/api "
#define CONFIG_AFLAGS_LLVM "--target=thumbv7m-none-eabi -mcpu=cortex-m4 -mfloat-abi=soft -mthumb -fPIC -fpie"
#define CONFIG_USR_LIB_SIGN_CFLAGS " -I../../externals/libecc/src "
#define CONFIG_USR_LIB_DFU 1
#define CONFIG_USB_DEV_SERIAL "123456789012345678901234"
#define CONFIG_LOADER_CONSOLE_USART1 1
#define CONFIG_KERNEL_EXPERT_MODE 1
#define CONFIG_USR_DRV_DRVISO7816_CFLAGS " -I@PROJFILES@/drivers/socs/stm32f439/drviso7816/api "
#define CONFIG_USR_LIB_USBCTRL_DIFFERENCIATE_DFU_FW_BUILD 1
#define CONFIG_USR_DRV_SPI 1
#define CONFIG_USR_DRV_CRYP 1
#define CONFIG_EXT_SECAES 1
#define CONFIG_APP_USB_STACKSIZE 32000
#define CONFIG_LIB_OPTIM_SIZE 1
#define CONFIG_BUILD_DIR "build"
#define CONFIG_USR_LIB_AES_DIFFERENCIATE_DFU_FW_BUILD 1
#define CONFIG_USR_LIB_GUI_MAX_TILE_NUMBER 32
#define CONFIG_USR_LIB_USBCTRL 1
#define CONFIG_LOADER_USE_BKPSRAM 1
#define CONFIG_ELF_NAME "$(CONFIG_PROJ_NAME).elf"
#define CONFIG_USR_LIB_SMARTCARD 1
#define CONFIG_MAXTASKS 8
#define CONFIG_SIG_TOKEN_PET_NAME "My fish name is Eve!"
#define CONFIG_HEX_NAME "$(CONFIG_PROJ_NAME).hex"
#define CONFIG_EXTERNALS 1
#define CONFIG_USR_LIB_CTAP 1
#define CONFIG_LOADER_FLASH_LOCK 1
#define CONFIG_AFLAGS_GCC "-mlittle-endian -mthumb -mcpu=cortex-m4 -mfloat-abi=soft -fPIC -fpie"
#define CONFIG_APP_USB_PERM_DEV_EXTI 1
#define CONFIG_SPI2 1
#define CONFIG_APP_USB_HEAPSIZE 0
#define CONFIG_USR_DRV_USART_CFLAGS " -I@PROJFILES@/drivers/socs/stm32f439/usart/api "
#define CONFIG_DMA_SHM 1
#define CONFIG_ARCH_CORTEX_M4 1
#define CONFIG_USR_LIB_DFU_CAN_DOWNLOAD 1
#define CONFIG_USR_LIB_HERPES 1
#define CONFIG_SCHED_PERIOD 10
#define CONFIG_USR_LIB_FIRMWARE_FLOP_ADDR 0x08120000
#define CONFIG_SOCNAME "stm32f439"
#define CONFIG_USR_DRV_FLASH_2M 1
#define CONFIG_USR_LIB_AES 1
#define CONFIG_CORENAME "cortex-m4"
#define CONFIG_PROJ_FILES "."
#define CONFIG_BOARDNAME "wookey"
#define CONFIG_DONE 1
#define CONFIG_AUTH_TOKEN_MAX_PIN 3
#define CONFIG_USR_LIB_FIRMWARE_BANK_SIZE 0xe0000
#define CONFIG_USR_LIB_ISO7816 1
#define CONFIG_USR_LIB_AES_DFU_ALGO_CRYP_SUPPORT_DMA 1
#define CONFIG_USR_LIB_DES 1
#define CONFIG_FIRMWARE_MODE_MONO_BANK 1
#define CONFIG_USR_LIB_FIRMWARE_FLIP_BOOTINFO_ADDR 0x08008000
#define CONFIG_OPTIM_SIZE 1
#define CONFIG_KERNEL_SOFTIRQ_QUEUE_DEPTH 20
#define CONFIG_KERNEL_MODE "debug"
#define CONFIG_WOOKEY 1
#define CONFIG_USR_LIB_SMARTCARD_CFLAGS " -I@PROJFILES@/libs/smartcard/api "
#define CONFIG_USR_LIB_MASSSTORAGE 1
#define CONFIG_KERNEL_DMA_ENABLE 1
#define CONFIG_LOADER_USE_PVD 1
#define CONFIG_USR_LIB_FIRMWARE 1
#define CONFIG_SIG_TOKEN_MAX_SC 10
#define CONFIG_USR_LIB_USBCTRL_DFU_DEV_PRODUCTID 0xCAFE
#define CONFIG_USR_LIB_USBHID 1
#define CONFIG_KERNEL_PANIC_FREEZE 1
#define CONFIG_USR_LIB_STD_CFLAGS " -I@PROJFILES@/libs/std/api "
#define CONFIG_USR_LIB_HMAC_CFLAGS " -I@PROJFILES@/libs/hmac/api "
#define CONFIG_USB_DEV_PRODNAME "wookey"
#define CONFIG_ECC_CURVNAME "SECP256R1"
#define CONFIG_DBGFLAGS_GCC "-ggdb -Os"
#define CONFIG_APP_USB_PERM_DEV_BUSES 1
#define CONFIG_USR_LIB_WOOKEY 1
#define CONFIG_AES256_CBC_ESSIV 1
#define CONFIG_DRV_OPTIM_SIZE 1
#define CONFIG_APP_USB_DOMAIN 0
#define CONFIG_DFU_TOKEN_MAX_SC 10
#define CONFIG_LOADER_SERIAL 1
#define CONFIG_DFU_TOKEN_USER_PIN 1234
#define CONFIG_USR_LIB_CCID_DEBUG 0
#define CONFIG_USBCTRL_FW_MAX_CTX 2
#define CONFIG_KERNEL_SERIAL 1
#define CONFIG_USR_DRV_SPI_CFLAGS " -I@PROJFILES@/drivers/socs/stm32f439/spi/api "
#define CONFIG_USR_LIB_HOTP_CFLAGS " -I@PROJFILES@/libs/hotp/api "
#define CONFIG_USR_LIB_GUI_MAX_MENU_NUMBER 12
#define CONFIG_USR_LIB_U2FAPDU 1
#define CONFIG_BOARD_RELEASE "v3"
#define CONFIG_LOADER_ERASE_WITH_RECOVERY 1
#define CONFIG_USR_DRV_USBOTGHS_CFLAGS " -I@PROJFILES@/drivers/socs/stm32f439/usbotghs/api "
#define CONFIG_ECC_CURVENAME_SP256 1
#define CONFIG_KERN_CFLAGS "-Os"
#define CONFIG_USR_LIB_GUI 1
#define CONFIG_KERNEL_ADA_BUILDSIZE "size"
#define CONFIG_USE_SIG_TOKEN "USE_SIG_TOKEN"
#define CONFIG_LOADER_FW_HASH_CHECK 1
#define CONFIG_USR_LIB_MASSSTORAGE_CFLAGS " -I@PROJFILES@/libs/massstorage/api "
#define CONFIG_USR_LIB_FIDO_EMULATE_USERPRESENCE 1
#define CONFIG_USR_LIB_HERPES_CFLAGS " -I@PROJFILES@/libs/herpes/api "
#define CONFIG_EMBEDCFLAGS "-Wl,--gc-sections -ffunction-sections -fno-builtin -ffreestanding -nostdlib -nodefaultlibs"
#define CONFIG_USR_LIB_CCID 1
#define CONFIG_USBCTRL_FW_MAX_CFG 1
#define CONFIG_USR_DRV_CRYP_CFLAGS " -I@PROJFILES@/drivers/socs/stm32f439/cryp/api "
#define CONFIG_WOOKEY_V3 1
#define CONFIG_DFU_TOKEN_MAX_PIN 3
#define CONFIG_KERNEL_CONSOLE_USART1 1
#define CONFIG_USR_LIB_AES_FW_ALGO_CRYP_SUPPORT 1
#define CONFIG_STD_MALLOC 1
#define CONFIG_USB_DEV_PRODNAME_INDEX 1
#define CONFIG_USR_LIB_FIDO_DEBUG 1
#define CONFIG_USR_LIB_USBCTRL_FW_DEV_PRODUCTID 0xCAFE
#define CONFIG_USR_DRV_AD7843 1
#define CONFIG_DFU_TOKEN_PET_PIN 1234
#define CONFIG_USR_LIB_FIRMWARE_CFLAGS " -I@PROJFILES@/libs/firmware/api "
#define CONFIG_KERNEL_USART 1
#define CONFIG_USR_LIB_MASSSTORAGE_SCSI_DEBUG 0
#define CONFIG_USR_LIB_MASSSTORAGE_SCSI_MAX_LUNS 1
#define CONFIG_STACKPROTFLAGS "-fstack-protector-strong"
#define CONFIG_APP_USB_PERM_TIM_GETCYCLES 2
#define CONFIG_DBGLEVEL 6
#define CONFIG_USR_LIB_CTAP_CTAP1 1
#define CONFIG_USB_DEV_SCSI_BLOCK_SIZE_4096 1
#define CONFIG_USR_LIB_USBCTRL_DEV_VENDORID 0xDEAD
#define CONFIG_USR_DRV_DRVISO7816 1
#define CONFIG_USR_LIB_DFU_CAN_UPLOAD 1
#define CONFIG_APP_USB_USR_DRV_USB_FS 1
#define CONFIG_SPI2_ROLE_MASTER 1
#define CONFIG_USB_DEV_REVISION "0001"
#define CONFIG_STM32F4 1
#define CONFIG_SCHED_SUPPORT_FISR 1
#define CONFIG_LOADER_USART 1
#define CONFIG_KERNEL_EWOK 1
#define CONFIG_USE_DIFFERENT_PHYSICAL_TOKENS 1
#define CONFIG_LOADER_INVAL_CFLOW_GOTO_ERROR 1
#define CONFIG_USR_LIB_AES_DFU_ALGO_CRYP_SUPPORT 1
#define CONFIG_USR_LIB_ISO7816_CFLAGS " -I@PROJFILES@/libs/iso7816/api "
#define CONFIG_WARNFLAGS_LLVM "-fintegrated-as -sed-command-line-argument -Wno-incompatible-library-redeclaration -Wall -Werror -Wextra -Wno-reserved-id-macro -Wno-padded -Wno-packed -Wno-covered-switch-default -Wno-used-but-marked-unused -Wno-unused-function -Werror"
#define CONFIG_IPC 1
#define CONFIG_KERN_OPTIM_SIZE 1
#define CONFIG_USB_DEV_SERIAL_INDEX 3
#define CONFIG_USR_LIB_CTAP_DEBUG 1
#define CONFIG_USR_LIB_USBHID_DEBUG 1
#define CONFIG_SIG_TOKEN_USER_PIN 1234
#define CONFIG_STD_MALLOC_ALIGN 8
#define CONFIG_STD_SANITIZE_HANDLERS 1
#define CONFIG_FIRMWARE 1
#define CONFIG_USBCTRL_DFU_MAX_CFG 1
#define CONFIG_RAM_SLOT_SIZE 16384
#define CONFIG_APP_USB_PERM_DEV_CRYPTO 0
#define CONFIG_STD_DRBG 1
#define CONFIG_APP_USB_FW 1
#define CONFIG_USR_LIB_SIGN 1
#define CONFIG_APP_USB_PERM_TSK_FISR 1
#define CONFIG_USR_LIB_STD 1
#define CONFIG_USR_LIB_AES_FW_ALGO_UNMASKED_TABLE 1
#define CONFIG_APPLETS 1
#define CONFIG_USBCTRL_DFU_MAX_CTX 2
#define CONFIG_SIG_TOKEN_MAX_PIN 3
#define CONFIG_ARCH_ARMV7M 1
#define CONFIG_USBCTRL_EP0_FIFO_SIZE 128
#define CONFIG_DEBUG 1
#define CONFIG_USR_LIB_AES_FW_ALGO_UNMASKED 1
#define CONFIG_PRIVATE_DIR "private"
#define CONFIG_STD_MALLOC_SIZE_LEN 16
#define CONFIG_ADA_PROFILE "zfp-stm32f4"
#define CONFIG_USR_LIB_MASSSTORAGE_BBB_DEBUG 0
#define CONFIG_AUTH_TOKEN_PET_NAME "My dog name is Bob!"
#define CONFIG_ADA_ARCH "arm-eabi"
#define CONFIG_USR_DRV_USBOTGFS_MODE_DEVICE 1
#define CONFIG_STM32F439 1
#define CONFIG_USB_DEV_MANUFACTURER "ANSSI"
#define CONFIG_WARNFLAGS_GCC "-Wl,--gc-sections -Wall -Werror -Wextra -Wno-reserved-id-macro -Wno-padded -Wno-packed -Wno-covered-switch-default -Wno-used-but-marked-unused -Wno-unused-but-set-variable -Wno-unused-function -Werror"
#define CONFIG_EC_UTILS "tools/ec_utils"
#define CONFIG_USR_DRV_AD7843_CFLAGS " -I@PROJFILES@/drivers/boards/wookey/ad7843/api "
#define CONFIG_USR_DRV_USB_HS 1
#define CONFIG_PROJ_NAME "u2f2"
#define CONFIG_USB_DEV_MANUFACTURER_INDEX 2
#define CONFIG_USR_DRV_HASH_CFLAGS " -I@PROJFILES@/drivers/socs/stm32f439/hash/api "
#define CONFIG_NEED_IPC 1
#define CONFIG_USR_DRV_USBOTGHS 1
#define CONFIG_USR_LIB_USBCDC 1
#define CONFIG_USR_LIB_USBCDC_CFLAGS " -I@PROJFILES@/libs/usbcdc/api "
