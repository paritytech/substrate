const logger = require('./logger')
/**
 * Wait n milliseconds
 *
 * @param n - In milliseconds
 */
function waitNMilliseconds (n) {
  return new Promise((resolve) => {
    setTimeout(resolve, n)
  })
}

/**
 * Run a function until that function correctly resolves
 *
 * @param fn - The function to run
 */
async function pollUntil (fn) {
  try {
    const result = await fn()

    return result
  } catch (_error) {
    logger.error('Error polling', _error)
    logger.debug('awaiting...')
    await waitNMilliseconds(5000) // FIXME We can add exponential delay here

    return pollUntil(fn)
  }
}

module.exports = { pollUntil, waitNMilliseconds }
