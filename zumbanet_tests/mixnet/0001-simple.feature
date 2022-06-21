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
#RACE
#bob: log line contains "Inject transaction from mixnet" within 100 seconds
#charlie: log line contains "Inject transaction from mixnet" within 100 seconds
#dave: log line contains "Inject transaction from mixnet" within 100 seconds
#eve: log line contains "Inject transaction from mixnet" within 100 seconds
#ferdie: log line contains "Inject transaction from mixnet" within 100 seconds
#ENDRACE

bob: js-script ./0001-send-custom.js with "surbs" return is equal to 1 within 20 seconds
bob: log line contains "Imported surb from" within 100 seconds

two: js-script ./0001-send-custom.js with "surbs" return is equal to 1 within 20 seconds
two: log line contains "Imported surb from" within 100 seconds
