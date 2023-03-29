#!/bin/sh

# meant to be installed via
#   git config filter.ci-prettier.clean "scripts/ci/gitlab/prettier.sh"

prettier --parser yaml
