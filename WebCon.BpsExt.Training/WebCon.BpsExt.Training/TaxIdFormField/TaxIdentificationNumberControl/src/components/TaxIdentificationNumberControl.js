import React, { PureComponent } from 'react';
import PropTypes from 'prop-types';
import CountryCodes from './CountryCodes';
import TaxIdentificationNumber from './TaxIdentificationNumber';

export default class TaxIdentificationNumberControl extends PureComponent {
    static propTypes = {
        model: PropTypes.any.isRequired,
        onChange: PropTypes.func.isRequired,
        fieldConfiguration: PropTypes.object.isRequired
    };

    constructor(props) {
        super(props);

        this.state = {
            countryCode: !this.props.model.CountryCode || this.props.model.CountryCode === '' ? this.props.model.CountryCodes[0] : this.props.model.CountryCode,
            taxIdentificationNumber: this.props.model.TaxIdentificationNumber
        };
    }

    handleCountryCodeChange = countryCode => {
        const { onChange } = this.props;
        const { taxIdentificationNumber } = this.state;

        const data = { CountryCodes: this.props.model.CountryCodes, CountryCode: countryCode, TaxIdentificationNumber: taxIdentificationNumber };

        onChange(data);
        this.setState({ countryCode: countryCode });
    }

    handleTaxIdentificationChange = taxIdentificationNumber => {
        const { onChange } = this.props;
        const { countryCode } = this.state;

        const data = { CountryCodes: this.props.model.CountryCodes, CountryCode: countryCode, TaxIdentificationNumber: taxIdentificationNumber };

        onChange(data);
        this.setState({ taxIdentificationNumber: taxIdentificationNumber });
    }

    render() {
        const fieldConfiguration = this.props.fieldConfiguration;
        const isDisabled = fieldConfiguration.isDisabled;
        const isAdmin = fieldConfiguration.isAdmin;
        const isReadonly = isDisabled && !isAdmin;

        return (
            <div style={{ display: 'flex' }}>
                <CountryCodes
                    onChange={this.handleCountryCodeChange}
                    isReadonly={isReadonly}
                    values={this.props.model.CountryCodes}
                    value={this.state.countryCode}
                />
                <TaxIdentificationNumber
                    onChange={this.handleTaxIdentificationChange}
                    isReadonly={isReadonly}
                    value={this.state.taxIdentificationNumber}
                />
            </div>
        );
    }
}