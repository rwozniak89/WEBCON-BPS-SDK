var emptyValueValidator_5f376110_80cc_11ea_a0b6_01e378cf750f = (function () {
    'use strict';

    var EmptyValueValidator = (function (_ref) {
      var model = _ref.model;

      if (!model || !model.TaxIdentificationNumber || model.TaxIdentificationNumber === '') {
        return false;
      }

      return true;
    });

    return EmptyValueValidator;

}());
window.webcon = window.webcon || {};
window.webcon.customControls = window.webcon.customControls || {};
window.webcon.customControls.emptyValueValidators = window.webcon.customControls.emptyValueValidators || {};
window.webcon.customControls.emptyValueValidators['5f376110-80cc-11ea-a0b6-01e378cf750f'] = emptyValueValidator_5f376110_80cc_11ea_a0b6_01e378cf750f;
