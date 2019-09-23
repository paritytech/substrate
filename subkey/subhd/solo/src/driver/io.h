SOLO_INTERNAL UINT32 gen_cmd(UINT8 cmd_index, UINT8* data, UINT16 data_len, UINT8* cmd, UINT16* len);

SOLO_INTERNAL UINT32 handle_cmd(UINT8* cmd, UINT16 cmd_len,UINT32 delays, UINT8* response, UINT16* len);

SOLO_INTERNAL UINT32 get_response(UINT8* response, UINT16* len);