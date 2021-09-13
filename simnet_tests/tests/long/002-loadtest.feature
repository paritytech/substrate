Feature: LoadTesting

  Scenario: spawn 50k transactions and wait their finalization
    Given a test network
    Then launch 'node' with parameters '/usr/local/bin/sub-flood --finalization --url ws://localhost:11222'
