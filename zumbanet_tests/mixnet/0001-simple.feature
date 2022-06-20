Description: Mixnet simple test 
Network: ./0001-simple.toml
Creds: config

# Some sanity checks
alice: is up
bob: is up
charlie: is up
dave: is up
eve: is up
ferdie: is up
one: is up
two: is up

# Mixnet running.
alice: log line contains "Mixnet running." within 100 seconds

alice: js-script ./0001-send-custom.js return is equal to 1 within 10 seconds
