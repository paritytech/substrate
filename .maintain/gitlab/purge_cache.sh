#!/bin/bash

set -ex

if [ -n "${PROJECT_NAME}" ] && [ -n "${CACHE_TYPE}" ] && [ -n "${BRANCH_NAME}" ]
then
    if [ -d "/ci-cache/${PROJECT_NAME}/${CACHE_TYPE}/${BRANCH_NAME}/${JOB_NAME}" ]
    then
        echo "Purging JOB cache in /ci-cache/${PROJECT_NAME}/${CACHE_TYPE}/${BRANCH_NAME}/${JOB_NAME} .";
        ls -l "/ci-cache/${PROJECT_NAME}/${CACHE_TYPE}/${BRANCH_NAME}";
    elif [ -d "/ci-cache/${PROJECT_NAME}/${CACHE_TYPE}/${BRANCH_NAME}" ]
    then
        echo "Purging BRANCH cache in /ci-cache/${PROJECT_NAME}/${CACHE_TYPE}/${BRANCH_NAME} .";
        ls -l "/ci-cache/${PROJECT_NAME}/${CACHE_TYPE}";
    else
        echo "Error! Directory /ci-cache/${PROJECT_NAME}/${CACHE_TYPE}/${BRANCH_NAME} does not exist.";
        exit 1;
    fi
else
    echo "Please set necessary variables.";
    exit 1;
fi
