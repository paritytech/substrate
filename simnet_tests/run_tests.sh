#!/bin/bash

### ARGS FOR THIS SCRIPT ###
# ./${SCRIPT_NAME} NAMESPACE IMAGE LOG_PATH FEATURES
#   NAMESPACE the kubernetes namespace where the test will run
#   IMAGE Substrate image used to spawn network
#   LOG_PATH path to dir where to save logs from external JS script that is run as part 
# of step in features file
#   FEATURES directory containing cucumber files or single  cucumber file that describes 
# what to test.   
#
# All args have default values, specify args to override
# e.g: ./${SCRIPT_NAME} test-name parity/substrate:latest logs quick

set -eou pipefail
SCRIPT_NAME="$0"
SCRIPT_PATH=$(dirname "${SCRIPT_NAME}")     # relative
SCRIPT_PATH=$(cd "${SCRIPT_PATH}" && pwd)   # absolutized and normalized

function random_string {
   head -1 <(fold -w 30  <(tr -dc 'a-z0-9' < /dev/urandom))
 }

#
### Script args
#

NAMESPACE=${1:-gurke-"$(random_string)"-runtest}
IMAGE=${2:-"parity/substrate:latest"}
LOG_PATH=${3:-"${SCRIPT_PATH}/logs"}
FEATURES=${4:-"ALL"}

mkdir -p "${SCRIPT_PATH}"/logs

echo "Running tests in namespace: ${NAMESPACE}"
echo "Testing image: ${IMAGE}"
echo "Storing scripts logs to: ${LOG_PATH}"
echo "Using features files from: ${FEATURES}"

#
### Script logic
#

function forward_port {
  # RUN_IN_CONTAINER is env var that is set in the dockerfile
  # use the -v operator to explicitly test if a variable is set
  if  [[ ! -v RUN_IN_CONTAINER  ]]  ; then 
    if is_port_forward_running ; then
      kill_previous_job
    fi
  fi
  start_forwading_job 
}

FORWARD_GREP_FILTER='kubectl.*[p]ort-forward.*svc/rpc.*11222'

function is_port_forward_running {
  # shellcheck disable=SC2009
  ps aux | grep -qE "${FORWARD_GREP_FILTER}" 
}

function kill_previous_job {
  # shellcheck disable=SC2009
  job_pid=$(ps aux | grep -E "${FORWARD_GREP_FILTER}" | awk '{ print $2 }')
  echo  "INFO Killed forwading port 9944 into bootnode"
  kill "${job_pid}"
}

function start_forwading_job {
  kubectl -n "${NAMESPACE}" \
          expose pod bootnode \
          --name=rpc \
          --type=NodePort \
          --target-port=9944 \
          --port=9944
  kubectl -n "${NAMESPACE}" \
          port-forward svc/rpc 11222:9944 &> "${LOG_PATH}/forward-${NAMESPACE}.log" &
  sleep 2
  echo "INFO Started forwading port 9944 into bootnode"
}

function update_api {
  echo "INFO: Updating Polkadot JS API"
  pwd
  cd "${SCRIPT_PATH}"/../../sub-flood/
  npm run build
  cd -
}

function run_test {
    case "${FEATURES}" in
      quick)         
        gurke test "${NAMESPACE}" "${SCRIPT_PATH}"/tests/quick  --log-path "${LOG_PATH}"
        ;;
      long)  
        gurke test "${NAMESPACE}" "${SCRIPT_PATH}"/tests/long   --log-path "${LOG_PATH}"
        ;;
      ALL )  
        gurke test "${NAMESPACE}" "${SCRIPT_PATH}"/tests        --log-path "${LOG_PATH}"
        ;;  
      ??* )  
        gurke test \
              "${NAMESPACE}" \
              "${SCRIPT_PATH}"/"${FEATURES}" \
              --log-path  "${LOG_PATH}"
        ;;  
    esac
}


export NAMESPACE="${NAMESPACE}"

set -x  # echo the commands to stdout
gurke spawn --config "${SCRIPT_PATH}"/configs/default_local_testnet.toml \
            -n "${NAMESPACE}" \
            --image "${IMAGE}"

echo "INFO: Checking if pods launched correctly"
kubectl -n "${NAMESPACE}" get pods -o wide

update_api

forward_port
run_test


