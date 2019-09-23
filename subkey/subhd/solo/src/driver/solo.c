#include "def.h"
#include "io.h"
#include "solo.h"
#include <stdio.h>

//#define INPUT_LOG

int solo_sign(unsigned char* msg, int ilen, unsigned char* sign)
{

    UINT8 data_buf[SOLO_MAX_LEN] = {0};
    UINT16 len = 0;
    UINT16 res_len = 0;
    UINT32 rv = 0;  
#ifdef INPUT_LOG
    UINT32 i = 0;
    printf("\n ************input********** %d\n", ilen);
    for(i=0;i<ilen;i++)
        printf("%x",msg[i]);
    printf("\n");
#endif
    rv = gen_cmd(SOLO_CMD_SIGN, msg, ilen, data_buf, &len);
    if (rv)
    {
        return SOLO_ERROR_PARA;
    }

    rv = handle_cmd(data_buf, len, SOLO_DELAY_COMMON, data_buf, &res_len); 
    if (rv)
    {
        return rv;
    }
    memcpy(sign,data_buf+SOLO_HEADER_LEN,res_len);
    return SOLO_OK;
} 

int solo_format()
{
    UINT8 data_buf[SOLO_MAX_LEN] = {0};
    UINT16 len = 0;
    UINT16 res_len = 0;
    UINT32 rv = 0;  

    rv = gen_cmd(SOLO_CMD_FORMAT, 0, 0, data_buf, &len);
    if (rv)
    {
        return SOLO_ERROR_PARA;
    }

    rv = handle_cmd(data_buf, len, SOLO_DELAY_COMMON, data_buf, &res_len); 
    if (rv)
    {
        return rv;
    }
    return SOLO_OK;
}

int solo_generate(unsigned char* seed)
{
    UINT8 data_buf[SOLO_MAX_LEN] = {0};
    UINT16 len = 0;
    UINT16 res_len = 0;
    UINT32 rv = 0;  

    rv = gen_cmd(SOLO_CMD_GEN, 0, 0, data_buf, &len);
    if (rv)
    {
        return SOLO_ERROR_PARA;
    }

    rv = handle_cmd(data_buf, len, SOLO_DELAY_COMMON, data_buf, &res_len); 
    if (rv)
    {
        return rv;
    }
    memcpy(seed,data_buf+SOLO_HEADER_LEN,res_len);
    return SOLO_OK;
}

int solo_pubkey(unsigned char* pk)
{
    UINT8 data_buf[SOLO_MAX_LEN] = {0};
    UINT16 len = 0;
    UINT16 res_len = 0;
    UINT32 rv = 0;  

    rv = gen_cmd(SOLO_CMD_GETPUB, 0, 0, data_buf, &len);
    if (rv)
    {
        return SOLO_ERROR_PARA;
    }

    rv = handle_cmd(data_buf, len, SOLO_DELAY_COMMON, data_buf, &res_len); 
    if (rv)
    {
        return rv;
    }
    memcpy(pk,data_buf+SOLO_HEADER_LEN,res_len);
    return SOLO_OK;
}

int solo_import(unsigned char* seed, unsigned int ilen)
{
    UINT8 data_buf[SOLO_MAX_LEN] = {0};
    UINT16 len = 0;
    UINT16 res_len = 0;
    UINT32 rv = 0;  
#ifdef INPUT_LOG
    UINT32 i = 0;
    printf("\n ************input********** %d\n", ilen);
    for(i=0;i<ilen;i++)
        printf("%x",seed[i]);
    printf("\n");
#endif
    rv = gen_cmd(SOLO_CMD_IMPORT, seed, ilen, data_buf, &len);
    if (rv)
    {
        return SOLO_ERROR_PARA;
    }

    rv = handle_cmd(data_buf, len, SOLO_DELAY_COMMON, data_buf, &res_len); 
    if (rv)
    {
        return rv;
    }

    return SOLO_OK;
}
