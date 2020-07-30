const api = require('./api')
module.exports = function (Hypervisor) {
  Object.assign(Hypervisor.prototype, api)
}
