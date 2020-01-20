# Substrate Prometheus Exporter
<<<<<<< HEAD

=======
![grants](./photo_2019-12-13_16-32-53.jpg)
>>>>>>> nodebreaker/prometheus_v0.3
## Introduction

Prometheus is one of the most widely used monitoring tool for managing highly available services supported by [Cloud Native Computing Foundation](https://www.cncf.io/). By providing Prometheus metrics in Substrate, node operators can easily adopt widely used display/alert tools such as Grafana and Alertmanager without setting-up/operating external Prometheus push gateways (which is an antipattern in the first place) through RPC connections. Easy access to such monitoring tools will benefit parachain developers/operators and validators to have much higher availability of their services.

## Table of Contents

Metrics

Start Prometheus
 - Edit Prometheus config file


## Metrics

Substrate can report and serve the Prometheus metrics, which in their turn can be consumed by Prometheus collector(s).

This functionality is disabled by default.

Metrics will be served under /metrics on 9615 port by default.


## Start Prometheus
### Edit Prometheus config file

You can visit [prometheus.yml](https://github.com/prometheus/prometheus/blob/master/documentation/examples/prometheus.yml) to download default `prometheus.yml`.

Then edit `prometheus.yml` and add `jobs` :

```yaml
      - job_name: kusama
          static_configs:
          - targets: ['localhost:9955']
            labels:
              instance: local-validator
```

> Note：value of targets is ip:port which used by substrate monitor 

### Start Prometheus

> The above example, you can save `prometheus.yml` at `~/volumes/prometheus` on your host machine

You can visit `http://localhost:9090` to see prometheus data.
