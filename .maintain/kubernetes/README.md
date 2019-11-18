

# Substrate Kubernetes Helm Chart

This [Helm Chart](https://helm.sh/) can be used for deploying containerized 
**Substrate** to a [Kubernetes](https://kubernetes.io/) cluster.


## Prerequisites

- Tested on Kubernetes 1.10.7-gke.6

## Installation

To install the chart with the release name `my-release` into namespace 
`my-namespace` from within this directory:

```console
$ helm install --namespace my-namespace --name my-release --values values.yaml ./
```

The command deploys Substrate on the Kubernetes cluster in the configuration 
given in `values.yaml`. When the namespace is omitted it'll be installed in 
the default one.


## Removal of the Chart

To uninstall/delete the `my-release` deployment:

```console
$ helm delete --namespace my-namespace my-release
```

The command removes all the Kubernetes components associated with the chart and deletes the release.


## Upgrading

Once the chart is installed and a new version should be deployed helm takes 
care of this by

```console
$ helm upgrade --namespace my-namespace --values values.yaml my-release ./
```


