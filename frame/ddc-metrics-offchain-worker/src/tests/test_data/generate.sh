#!/usr/bin/env bash

# These commands were used to get sample data from DDC nodes.
# The data was modified to simplify testing.

curl https://node-0.ddc.stage.cere.network/api/rest/nodes | json_pp > ddc_nodes.json

curl "https://node-0.ddc.stage.cere.network/api/rest/metrics?isMaster=true&active=true" | json_pp > ddc_metrics_node-0.json

curl "https://node-3.ddc.stage.cere.network/api/rest/metrics?isMaster=true&active=true" | json_pp > ddc_metrics_node-3.json
