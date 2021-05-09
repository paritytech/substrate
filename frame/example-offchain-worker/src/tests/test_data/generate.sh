#!/usr/bin/env bash

# These commands were used to get sample data from DDC nodes.
# The data was modified to simplify testing.

curl https://node-0.ddc.stage.cere.network/api/rest/nodes | json_pp > ddc_nodes.json

curl https://node-0.ddc.stage.cere.network/api/rest/metrics | json_pp > ddc_metrics.json

curl https://node-0.ddc.stage.cere.network/api/rest/partitions | json_pp > ddc_partitions.json

curl "https://node-0.ddc.stage.cere.network/api/rest/metrics?appPubKey=0x00a2e826451b78afb99241b1331e7594526329225ff8937dbc62f43ec20d1830&partitionId=0cb0f451-255b-4a4f-918b-6c34c7047331&from=0&to=0" | json_pp > ddc_metrics_0c.json

curl "https://node-3.ddc.stage.cere.network/api/rest/metrics?appPubKey=0x00a2e826451b78afb99241b1331e7594526329225ff8937dbc62f43ec20d1830&partitionId=f6cbe4e6-ef3a-4970-b3da-f8ae29cd22bd&from=0&to=0" | json_pp > ddc_metrics_f6.json

curl "https://node-0.ddc.stage.cere.network/api/rest/metrics?appPubKey=0x100ad4097b6e60700a5d5c5294cb6d663090ef5f547e84cc20ec6bcc7a552f13&partitionId=d9fb155d-6e15-44c5-8d71-ff22db7a0193&from=0&to=0" | json_pp > ddc_metrics_d9.json
