import React, { PureComponent } from 'react';
import PropTypes from 'prop-types';

export default class TaxIdentificationNumber extends PureComponent {
    static propTypes = {
        isReadonly: PropTypes.bool.isRequired,
        value: PropTypes.string.isRequired,
        onChange: PropTypes.func.isRequired
    };

    handleChange = event => {
        const { onChange } = this.props;
        const value = event.target.value;

        onChange(value);
    }

    render() {
        return (
            <>
                <input type='text'
                    className='wfFormControl form-control'
                    disabled={this.props.isReadonly}
                    value={this.props.value}
                    onChange={this.handleChange}
                />
            </>
        );
    }
}