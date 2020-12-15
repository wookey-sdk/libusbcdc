/*
 *
 * Copyright 2019 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#ifndef USBCDC_DESCRIPTOR_H_
#define USBCDC_DESCRIPTOR_H_

#include "libc/types.h"
#include "libc/stdio.h"
#include "libc/syscall.h"
#include "api/libusbcdc.h"
#include "libusbctrl.h"
#include "autoconf.h"

typedef enum {
    CS_INTERFACE_DESC  = 0x24,
    CS_ENDPOINT_DESC   = 0x25
} cs_descriptor_type_t;

/***************************************************
 * CDC class descriptors
 */
#define CDC_VERSION 0x0110 /* 1.1 */

#define CDC_VERSION_Lo 0x01 /* 1.1 */
#define CDC_VERSION_Hi 0x10 /* 1.1 */


typedef enum {
    CS_FUNCTIONAL_HEADER = 0,  /*< Header of functional descriptors */
    CS_FUNCTIONAL_CALL   = 1,  /*< Call Management descriptor */
    CS_FUNCTIONAL_ACM    = 2,   /*< Abstract Control Management descriptor */
    CS_FUNCTIONAL_DLM    = 3,   /*< Direct line management descriptor */
    CS_FUNCTIONAL_TR     = 4,   /*< Telephone Ringer descriptor */
    CS_FUNCTIONAL_TLLS   = 5,   /*< Telephone call & Line state descriptor */
    CS_FUNCTIONAL_UNION  = 6,   /*< Union functional descriptor */
    CS_FUNCTIONAL_CS     = 7,   /*< Country selection functional descriptor */
    CS_FUNCTIONAL_TOM    = 8,   /*< Telephone operational modes descriptor */
    CS_FUNCTIONAL_UT     = 9,   /*< USB Terminal functional descriptor */
    CS_FUNCTIONAL_NC     = 0xa, /*< Network channel functional descriptor */
    CS_FUNCTIONAL_PU     = 0xb, /*< Protocol Unit functional descriptor */
    CS_FUNCTIONAL_EU     = 0xc, /*< Extention Unit functional descriptor */
    CS_FUNCTIONAL_MCM    = 0xd, /*< Multi_channel management functional descriptor */
    CS_FUNCTIONAL_CAPI   = 0xe, /*< CAPI control management functional descriptor */
    CS_FUNCTIONAL_ETH    = 0xf, /*< Ethernet networking functional descriptor */
    CS_FUNCTIONAL_ATM    = 0x10 /*< ATM networking functional descriptor */
    /* other (0x11->0xff) are reserved */
} cs_interface_desc_id_t;

/**********************************************************
 * CDC class functional descriptors declaration
 *
 * (See usbcdc 1.1 chap 5.2.3 for full description and definitions)
 */

typedef struct __packed {
    uint8_t bLength;
    uint8_t bDescriptorType;
    uint8_t bDescriptorSubtype;
    uint8_t bcdCDC_hi; /*CDC spec release */
    uint8_t bcdCDC_lo; /*CDC spec release */
} header_functional_desc_t;


typedef enum {
    CALL_MGMT_CAPA_NONE = 0,
    CALL_MGMT_CAPA_HANDLED_BY_DEVICE = 1,
    CALL_MGMT_CAPA_HANDLED_OVER_DATA_IFACE = 2
} call_mgmt_capabilities_t;

typedef struct __packed {
    uint8_t bFunctionLength;
    uint8_t bDescriptorType;
    uint8_t bDescriptorSubtype;
    /* bitmap:
     * D0=0: device does not handle call mgmt itself, D0=1: device handle call mgmt itelf
     * D1=0: device send/rcv call mgmt info only over Communication class iface, D1=1: device can recv call mgmt over data iface
     * D7..D2: RESERVED (set to 0)
     */
    uint8_t bmCapabilities;
    uint8_t bDataInterface; /*iface number of Data iface optionaly used (D1=1) */
} call_mgmt_functional_desc_t;



typedef enum {
    ACM_CAPA_NONE = 0,
    ACM_CAPA_COMM_FEATURES_SUPPORT = 1,
    ACM_CAPA_LINE_CODING_SUPPORT = 2,
    ACM_CAPA_BREAK_SUPPORT = 4,
    ACM_CAPANETCON_SUPPORT = 8
} acm_capabilities_t;

typedef struct __packed {
    uint8_t bFunctionLength;
    uint8_t bDescriptorType;
    uint8_t bDescriptorSubtype;
    /* bitmap:
     * D0=1: support for [set_comm_feature, Clear_comm_feature, Get_comm_feature]
     * D1=1: support for [set_line_coding, set_ctrl_line_state, get_line_coding, notif:serial_state]
     * D2=1: support for [send_break]
     * D3=1: support for [notif:network_connection]
     * D7..D4: RESERVED (set to 0)
     */
    uint8_t bmCapabilities;
} acm_functional_desc_t;

typedef struct __packed {
    uint8_t bFunctionLength;
    uint8_t bDescriptorType;
    uint8_t bDescriptorSubtype;
    uint8_t bmCapabilities;
} dlm_functional_desc_t;

typedef struct __packed {
    uint8_t bFunctionLength;
    uint8_t bDescriptorType;
    uint8_t bDescriptorSubtype;
    uint8_t bRingerVolSteps;
    uint8_t bNumRingerPatterns;
} tr_functional_desc_t;

typedef struct __packed {
    uint8_t bFunctionLength;
    uint8_t bDescriptorType;
    uint8_t bDescriptorSubtype;
    uint8_t bmCapabilities;
} tom_functional_desc_t;

typedef struct __packed {
    uint8_t  bFunctionLength;
    uint8_t  bDescriptorType;
    uint8_t  bDescriptorSubtype;
    uint32_t bmCapabilities;
} tcls_functional_desc_t;

typedef struct __packed {
    uint8_t bFunctionLength;
    uint8_t bDescriptorType;
    uint8_t bDescriptorSubtype;
    uint8_t bMasterInterface; /*< iface number of the data or comm iface designed as the master or controlling iface of the union.
                                (zero-based index of the interface in this configuration (bInterfaceNum)) */
    uint8_t bSlaveInterface0; /*< iface number of the first slave interface (FIXME: CDC may support multiple slave interfaces) */
} union_functional_desc_t;

typedef struct __packed {
    uint8_t bFunctionLength;
    uint8_t bDescriptorType;
    uint8_t bDescriptorSubtype;
    uint8_t iCountryCodeRefDate; /* String index for ISO3166 date string (ddmmyyyyy) */
    uint16_t wCountryCode[];     /* Country Cocd in ISO3166 for each supported country */
} cs_functional_desc_t;

/* TODO: continuing all functional descriptor definition */

/*********************
 * CDC/ACM case for tty header
 */

typedef struct __packed {
    header_functional_desc_t    header;
    call_mgmt_functional_desc_t call;
    acm_functional_desc_t       acm;
    union_functional_desc_t     un;
} full_functional_desc_t;


mbed_error_t      usbcdc_get_descriptor(uint8_t             iface_id,
                                        uint8_t            *buf,
                                        uint8_t            *desc_size,
                                        uint32_t            usbdci_handler __attribute__((unused)));


#endif/*!USB_DESCRIPTOR_H_*/
