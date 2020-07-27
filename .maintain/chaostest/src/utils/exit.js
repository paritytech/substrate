const logger = require('../utils/logger')

const succeedExit = function () {
  process.exit(0)
}

const errorExit = function (msg, err) {
  logger.error(msg, err)
  process.exit(1)
}

module.exports = { succeedExit, errorExit }
