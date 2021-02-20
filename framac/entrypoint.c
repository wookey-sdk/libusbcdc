#include "autoconf.h"
#include "libc/types.h"
#include "libc/string.h"
#include "generated/devlist.h"
#include "libusbctrl.h"
#include "api/libusbcdc.h"
#include "usbcdc.h"
#include "usbcdc_requests.h"
#include "framac/entrypoint.h"

#define USB_BUF_SIZE 16384

/* NOTE: alignment for DMA */
__attribute__ ((aligned(4)))
         uint8_t usb_buf[USB_BUF_SIZE] = { 0 };

/*
 * Support for Frama-C testing
 */

/*@
  @ assigns \nothing;
  */
void Frama_C_update_entropy_b(void) {
  Frama_C_entropy_source_b = Frama_C_entropy_source_b;
}


/*@
  @ assigns \nothing;
  */
void Frama_C_update_entropy_8(void) {
  Frama_C_entropy_source_8 = Frama_C_entropy_source_8;
}

/*@
  @ assigns \nothing;
  */
void Frama_C_update_entropy_16(void) {
  Frama_C_entropy_source_16 = Frama_C_entropy_source_16;
}

/*@
  @ assigns \nothing;
  */
void Frama_C_update_entropy_32(void) {
  Frama_C_entropy_source_32 = Frama_C_entropy_source_32;
}


/*@
  @ assigns \nothing;
  */
bool Frama_C_interval_b(bool min, bool max)
{
  bool r,aux;
  Frama_C_update_entropy_b();
  aux = Frama_C_entropy_source_b;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}



/*@
  @ assigns \nothing;
  */
uint8_t Frama_C_interval_8(uint8_t min, uint8_t max)
{
  uint8_t r,aux;
  Frama_C_update_entropy_8();
  aux = Frama_C_entropy_source_8;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}


/*@
  @ assigns \nothing;
  */
uint16_t Frama_C_interval_16(uint16_t min, uint16_t max)
{
  uint16_t r,aux;
  Frama_C_update_entropy_16();
  aux = Frama_C_entropy_source_16;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*@
  @ assigns \nothing;
  */
uint32_t Frama_C_interval_32(uint32_t min, uint32_t max)
{
  uint32_t r,aux;
  Frama_C_update_entropy_32();
  aux = Frama_C_entropy_source_32;
  if ((aux>=min) && (aux <=max))
    r = aux;
  else
    r = min;
  return r;
}

/*

 test_fcn_usbctrl : test des fonctons définies dans usbctrl.c avec leurs paramètres
 					correctement définis (pas de débordement de tableaux, pointeurs valides...)

*/

/*********************************************************************
 * Callbacks implementations that are required by libmassstorage API
 */

mbed_error_t variable_errcode;

/*@
  @ assigns \nothing;
  */
void usbctrl_configuration_set(void)
{
}


/*@
  @ assigns \nothing;
  */
mbed_error_t backend_receive_frame(uint8_t cdcid __attribute__((unused)), uint8_t*buf __attribute__((unused)), uint16_t len __attribute__((unused)))
{
    return MBED_ERROR_NONE;
}

mbed_error_t backend_frame_sent(uint8_t cdc_id __attribute__((unused))) {
    return MBED_ERROR_NONE;
}

mbed_error_t cdc_ctrl_sent(uint8_t cdcid __attribute__((unused)))
{
    return MBED_ERROR_NONE;
}

/*********************************************************************
 * Effective tests functions
 */

uint32_t usbxdci_handler = 0;
uint8_t cdc_handler = 0;
uint8_t in_buff[64];
uint32_t in_buff_len = 64;



mbed_error_t prepare_ctrl_ctx(void)
{
    bool stty_mode = Frama_C_interval_b(0,1);
    mbed_error_t errcode;
    errcode = usbctrl_declare(USB_OTG_HS_ID, &usbxdci_handler);

    /* TODO: reimplement malloc properly ! */
    wmalloc_init();
    /*
     * Let's declare a CDC/ACM device (TODO)
     */

    usbcdc_declare(usbxdci_handler, 64, &cdc_handler, in_buff, in_buff_len);
    usbcdc_configure(cdc_handler, stty_mode, backend_receive_frame, backend_frame_sent, cdc_ctrl_sent);
    usbcdc_initialize(cdc_handler);
    return errcode;
}



void test_fcn_cdc(){
    uint8_t ep = Frama_C_interval_8(1,3);
    uint32_t size = Frama_C_interval_32(1,64);

    usbcdc_recv_data(cdc_handler);

    usbcdc_exec(cdc_handler);
    usb_data_ep_handler(USB_OTG_HS_ID, size, ep);
    usbcdc_exec(cdc_handler);

    usbcdc_recv_data(cdc_handler);
    usb_data_ep_handler(USB_OTG_HS_ID, size, ep);
    usbcdc_exec(cdc_handler);

    usbctrl_setup_pkt_t pkt;
    pkt.bRequest = Frama_C_interval_8(0,255);
    pkt.wLength = Frama_C_interval_16(0,100); /* enough for coverage */
    pkt.wIndex = Frama_C_interval_16(0,5); /* not used, enough for coverage */
    pkt.bmRequestType = Frama_C_interval_8(0,255);
    usbcdc_class_rqst_handler(USB_OTG_HS_ID, &pkt);

    usbcdc_exec(cdc_handler);
    usbcdc_class_rqst_handler(USB_OTG_HS_ID, &pkt);
    usbcdc_exec(cdc_handler);
    usbcdc_send_data(cdc_handler, &in_buff[0], size);
    usbcdc_recv_data(cdc_handler);
}

void test_fcn_cdc_errorcases(){
    return;
}

int main(void)
{
    variable_errcode = Frama_C_interval_8(0,16);
    mbed_error_t errcode;

    errcode = prepare_ctrl_ctx();
    if (errcode != MBED_ERROR_NONE) {
        goto err;
    }
    test_fcn_cdc() ;
    test_fcn_cdc_errorcases() ;
err:
    return errcode;
}
