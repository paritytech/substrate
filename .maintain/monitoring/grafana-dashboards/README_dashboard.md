## Substrate Dashboard

Shared templated Grafana dashboards.

To import the dashboards follow the [Grafana
documentation](https://grafana.com/docs/grafana/latest/reference/export_import/).
You can see an example setup [here](../../../.maintain/sentry-node).

#### Required labels on Prometheus metrics

- `instance` referring to a single scrape target (see [Prometheus docs for
  details](https://prometheus.io/docs/concepts/jobs_instances/)).

- `network` referring to the Blockchain network e.g. Kusama.
