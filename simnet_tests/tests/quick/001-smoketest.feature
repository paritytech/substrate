Feature: Smoketest

  Scenario: Minimal Example
    Given a test network
    Then alice is up
    And alice reports substrate_node_roles is 4
    And alice reports substrate_sub_libp2p_is_major_syncing is 0
    When alice's best block should be above 30
    Then alice reports block height is greater than 30
    And alice reports peers count is at least 2
    Then bob is up
    And bob reports block height is greater than 30
    And bob reports peers count is at least 2
    Then charlie is up
    And charlie reports block height is greater than 30
    And charlie reports peers count is at least 2
