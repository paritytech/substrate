### Check device

```
sudo dmesg | grep ttyS*
```

### Clear device to empty

```
sudo ./subkey hard-format
```

### Generate new keypair

```
sudo ./subkey hard-gen
```
The hex seed will be given out only with this command

### Get public key and address

```
sudo ./subkey hard-getpub
```

### Sign data

```
echo -n '##..##' | sudo ./subkey hard-sign
//example
//echo -n '12' | sudo ./subkey hard-sign

signature: d040391f9c3642070f71310ee2ee7be09c694c0ceb5667941d960ba649fcea75bca37a9730700fd0bc3ebd31921d583cf962aa3f6ee6d658f2eed92e573e1e8d

//verify it with
echo -n '12' | sudo ./subkey verify d040391f9c3642070f71310ee2ee7be09c694c0ceb5667941d960ba649fcea75bca37a9730700fd0bc3ebd31921d583cf962aa3f6ee6d658f2eed92e573e1e8d 0x42f7f323ae819c76f7061301b16f016bc6c815eac48d64a9d50ebaac622f8532
Signature verifies correctly.
```

### Sign transfer

```
sudo ./subkey hard-transfer [address] [amount] [nonce]

//example
//sudo ./subkey hard-transfer 5DaWg3eDdG7HXoZMoembiB2RL65i5a3ehWdwbh7BKSTqDRjo 1001
 0
```

## Import seed

```
echo -n -e '\x##..\x##' | sudo ./subkey hard-import 
```