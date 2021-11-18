import React, { PureComponent } from 'react';
import PropTypes from 'prop-types';

export default class CountryCodes extends PureComponent {
    static propTypes = {
        isReadonly: PropTypes.bool.isRequired,
        values: PropTypes.array.isRequired,
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
                <select style={{ width: '15%', marginRight: '3px' }}
                    disabled={this.props.isReadonly} 
                    className='dropdown form-control' 
                    onChange={this.handleChange}
                    selected>
                    {
                        this.props.values.map(countryCode => {
                            if (countryCode === this.props.value)
                                return <option key={countryCode} value={countryCode} selected>{countryCode}</option>;
                            return <option key={countryCode} value={countryCode}>{countryCode}</option>;
                        })
                    }
                </select>
            </>
        );
    }
}