#ifndef __SOLO_DEF_
#define __SOLO_DEF_

typedef unsigned int UINT32;
typedef unsigned short UINT16;
typedef unsigned char UINT8;
#define IN
#define OUT


#define SOLO_INTERNAL
//LEN && size & time
#define SOLO_MAX_LEN            256
#define SOLO_HEADER_LEN         8
#define SOLO_CRC_LEN            2
#define SOLO_SIMPLE_CMD_LEN     10
#define SOLO_DELAY_LONG         2000000 //2s
#define SOLO_DELAY_MID          500000 //500mss
#define SOLO_DELAY_COMMON       100000   //50ms  

//PACKAGE HEADER
//////OFFSET
#define SOLO_SYNC_OFFSET        0
#define SOLO_CMD_OFFSET         3
#define SOLO_COMM_OFFSET        4
#define SOLO_OP_OFFSET          5
#define SOLO_LEN_OFFSET         6
#define SOLO_DATA_OFFSET        8
//////const value
#define SOLO_SYNC_1             0x55
#define SOLO_SYNC_2             0xaa
//////command
#define SOLO_CMD_TRANSFER       0
#define SOLO_CMD_SIGN           1
#define SOLO_CMD_GEN            2
#define SOLO_CMD_IMPORT         3
#define SOLO_CMD_GETPUB         4
#define SOLO_CMD_FORMAT         5

//Error code
#define SOLO_OK                     0
#define SOLO_ERROR_PARA             0x80
#define SOLO_ERROR_COMM             0x81
#define SOLO_ERROR_DEVICE           0x82
#define SOLO_ERROR_NO_FINGER        0x83
#define SOLO_ERROR_CRC              0x84
//enroll status
#define SOLO_STATUS_TIMEOUT         0x12
#define SOLO_STATUS_REDUNANT        0x19
#define SOLO_STATUS_BAD             0x20
#define SOLO_STATUS_GOOD            0x21
#define SOLO_STATUS_WAIT            0x25
#define SOLO_STATUS_WERID           0x26
#define SOLO_STATUS_QUICK           0x27
#define SOLO_STATUS_PART            0x28
#define SOLO_STATUS_IDLE            0x3f

//identify
#define SOLO_STATUS_MATCH           0x00
#define SOLO_STATUS_NOT_MATCH       0x01

#include "os_uart.h"
#include <unistd.h> //sleep
#include <string.h> //memcpy


#endif