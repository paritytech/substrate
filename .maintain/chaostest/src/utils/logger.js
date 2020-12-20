const winston = require('winston')
const fs = require('fs')
const logDir = 'log' // Or read from a configuration
const { format, transports } = winston
const env = process.env.NODE_ENV || 'development'
const util = require('util')

if (!fs.existsSync(logDir)) {
  // Create the directory if it does not exist
  fs.mkdirSync(logDir)
}

const logFormat = format.printf(info => {
  info.message = util.format(info.message)
  if (info.metadata && Object.keys(info.metadata).length) {
    info.message = util.format(info.message, info.metadata)
  }
  return `${info.timestamp} ${info.level}: ${info.message}`
})

const logger = winston.createLogger({
  level: env === 'development' ? 'debug' : 'info',
  transports: [
    new transports.Console({
      format: format.combine(
        format.timestamp({ format: 'YYYY-MM-DD HH:mm:ss' }),
        // Format the metadata object
        format.metadata({ fillExcept: ['message', 'level', 'timestamp', 'label'] }),
        format.colorize(),
        logFormat
      )
    }),
    new winston.transports.File({
      level: env === 'development' ? 'debug' : 'info',
      filename: logDir + '/logs.log',
      format: format.combine(
        format.timestamp(),
        format.json()
      ),
      maxsize: 1024 * 1024 * 10 // 10MB
    })
  ],
  exceptionHandlers: [
    new winston.transports.File({
      filename: 'log/exceptions.log'
    })
  ]
})

module.exports = logger
