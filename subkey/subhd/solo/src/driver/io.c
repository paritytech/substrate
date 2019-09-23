#include "def.h"
#include "uart.h"
#include "crc.h"
#include "io.h"

SOLO_INTERNAL UINT32 gen_cmd(UINT8 cmd_index, UINT8* data, UINT16 data_len, UINT8* cmd, UINT16* len)
{
    UINT8 header[SOLO_HEADER_LEN] = {SOLO_SYNC_1, SOLO_SYNC_2, 0, 0, 0, 0, 0, 0};
    UINT8 crc[SOLO_CRC_LEN] = { 0 };
    UINT32 rv = 0
    ;
    //para check
    if(data_len > 0x1000)
        return SOLO_ERROR_PARA;
    if(cmd==0)
        return SOLO_ERROR_PARA;
    //gen header
    header[SOLO_CMD_OFFSET] = cmd_index;
    if(data_len>0)
    {
        header[SOLO_LEN_OFFSET] = (UINT8)((data_len>>8)&0x00ff);
        header[SOLO_LEN_OFFSET+1] = (UINT8)(data_len&0x00ff);
    }
    memcpy(cmd,header,SOLO_HEADER_LEN);
    //gen data if have
    if(data_len>0&&data!=0)
    {
        memcpy(cmd+SOLO_HEADER_LEN,data, data_len);
    }
    //gen crc
    rv = calc_crc(cmd,SOLO_HEADER_LEN+data_len,crc);
    if (rv)
        return SOLO_ERROR_CRC;
    memcpy(cmd+SOLO_HEADER_LEN+data_len,crc,SOLO_CRC_LEN);

    
    *len = SOLO_HEADER_LEN + data_len + SOLO_CRC_LEN;

    return SOLO_OK;
}


SOLO_INTERNAL UINT32 handle_cmd(UINT8* cmd, UINT16 cmd_len,UINT32 delays, UINT8* response, UINT16* len)
{
    UINT32 rv = 0;
    UINT16 l = 0;
    rv = SOLO_uart_write(cmd, cmd_len);
    if (rv)
        return SOLO_ERROR_COMM;

    usleep(delays);

    rv = SOLO_uart_read(response, SOLO_SIMPLE_CMD_LEN);
    if (rv)
        return SOLO_ERROR_COMM;
    //sync

    if (response[SOLO_COMM_OFFSET] != SOLO_OK)
        return response[SOLO_COMM_OFFSET];
    if (response[SOLO_OP_OFFSET] != SOLO_OK)
        return response[SOLO_OP_OFFSET];
    l = response[SOLO_LEN_OFFSET]*256 + response[SOLO_LEN_OFFSET+1];
    if(l>0)
    {
        rv = SOLO_uart_read(response+SOLO_SIMPLE_CMD_LEN, l);
        if (rv)
            return SOLO_ERROR_COMM;
    }
  // rv = check_crc(response, SOLO_HEADER_LEN+l, response + SOLO_HEADER_LEN+l);
  //  if (rv)
  //      return SOLO_ERROR_CRC;

 
    *len = l;
   
   return SOLO_OK;
   
}

SOLO_INTERNAL UINT32 get_response(UINT8* response, UINT16* len)
{
    UINT16 l = 0;
    UINT32 rv = 0;
    usleep(SOLO_DELAY_COMMON);
    
    rv = SOLO_uart_read(response, SOLO_SIMPLE_CMD_LEN);
    if (rv)
        return SOLO_ERROR_COMM;

    if (response[SOLO_COMM_OFFSET] != SOLO_OK)
        return response[SOLO_COMM_OFFSET];
    if (response[SOLO_OP_OFFSET] != SOLO_OK)
        return response[SOLO_OP_OFFSET];
    l = response[SOLO_LEN_OFFSET]*256 + response[SOLO_LEN_OFFSET+1];
    if(l>0)
    {
        rv = SOLO_uart_read(response+SOLO_SIMPLE_CMD_LEN, l);
        if (rv)
            return SOLO_ERROR_COMM;
    }
   rv = check_crc(response, SOLO_HEADER_LEN+l, response + SOLO_HEADER_LEN+l);
    if (rv)
        return SOLO_ERROR_CRC;

    if(l>0&&len!=0)
        *len = l;
   
   return SOLO_OK;
}