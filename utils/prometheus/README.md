# Substrate Prometheus Exporter

## Introduction

[Prometheus](https://prometheus.io/) is one of the most widely used monitoring tools for managing highly available services supported by [Cloud Native Computing Foundation](https://www.cncf.io/). By providing Prometheus metrics in Substrate, node operators can easily adopt widely used display/alert tools such
as [Grafana](https://grafana.com/) and [Alertmanager](https://prometheus.io/docs/alerting/alertmanager/). Easy access to such monitoring tools will benefit parachain developers/operators and validators to have much higher availability of their services.

Metrics will be served under `/metrics` on TCP port 9615 by default.

## Quick Start
 
1. From the root of the repository start Substrate `cargo run --release`.

2. In another terminal run `curl localhost:9615/metrics` to retrieve the metrics.

To learn how to configure Prometheus see the Prometheus [Getting Started](https://prometheus.io/docs/prometheus/latest/getting_started/) guide.