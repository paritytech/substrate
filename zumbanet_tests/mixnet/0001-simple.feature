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

alice: js-script ./0001-send-custom.js return is equal to 1 within 20 seconds

# one of? how?
RACE
bob: log line contains "Inject transaction from mixnet" within 100 seconds
charlie: log line contains "Inject transaction from mixnet" within 100 seconds
dave: log line contains "Inject transaction from mixnet" within 100 seconds
eve: log line contains "Inject transaction from mixnet" within 100 seconds
ferdie: log line contains "Inject transaction from mixnet" within 100 seconds
ENDRACE
#ferdie: log line contains "Received from surb." within 100 seconds
