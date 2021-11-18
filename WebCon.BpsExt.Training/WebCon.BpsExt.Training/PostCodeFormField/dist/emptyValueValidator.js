var emptyValueValidator_bc19c114_ba5b_4fb1_a7cf_fe4f8709c052 = (function () {
    'use strict';

    var EmptyValueValidator = (function (_ref) {
      var model = _ref.model,
          sdkConfiguration = _ref.sdkConfiguration,
          fieldConfiguration = _ref.fieldConfiguration;

      if (!model || typeof model !== 'string') {
        return false;
      }

      return true;
    });

    return EmptyValueValidator;

}());
window.webcon = window.webcon || {};
window.webcon.customControls = window.webcon.customControls || {};
window.webcon.customControls.emptyValueValidators = window.webcon.customControls.emptyValueValidators || {};
window.webcon.customControls.emptyValueValidators['bc19c114-ba5b-4fb1-a7cf-fe4f8709c052'] = emptyValueValidator_bc19c114_ba5b_4fb1_a7cf_fe4f8709c052;
