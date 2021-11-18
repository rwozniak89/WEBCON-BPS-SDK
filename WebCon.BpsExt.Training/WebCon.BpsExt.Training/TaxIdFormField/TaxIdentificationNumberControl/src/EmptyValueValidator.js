export default ({ model }) => {
    if (!model || !model.TaxIdentificationNumber || model.TaxIdentificationNumber === '') {
        return false;
    }

    return true;
};
