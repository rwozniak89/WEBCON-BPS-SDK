const postCodePattern = /^\d{2}-(\d{3})?$/;

export default ({ model, sdkConfiguration, fieldConfiguration }) => {
    if (!model || (typeof model === 'string' && model === '')) {
        return {
            isValid: true,
        };
    } else if (typeof model !== 'string') {
        return {
            isValid: false,
            errorMessage: 'Invalid model',
        };
    }

    return {
        isValid: postCodePattern.test(model),
        errorMessage:
            "Value must match the pattern 'XX-XXX' where X is a digit",
    };
};
