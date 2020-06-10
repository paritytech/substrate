const deployment = require('./deployment')
module.exports = function (Hypervisor) {
  Object.assign(Hypervisor.prototype, deployment)
}
