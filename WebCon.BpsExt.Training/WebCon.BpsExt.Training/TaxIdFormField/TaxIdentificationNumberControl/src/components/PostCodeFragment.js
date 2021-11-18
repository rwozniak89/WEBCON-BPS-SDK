import classNames from 'classnames';
import React, { PureComponent } from 'react';
import PropTypes from 'prop-types';

const allowed = [
    9, // Tab
    33, // Pg Up
    34, // Pg Down
    35, // End
    36, // Home
    37, // Arrow
    38, // Arrow
    39, // Arrow
    40, // Arrow
];

const allowedChars = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];

const allowedWithoutShift = [
    8, // Backspace
    13, // Enter
    27, // Esc
    45, // Ins
    46, // Del
];

const allowedWithoutShiftChars = [
    109, // Numpad minus
    110, // Numpad dot
    173, // - (Firefox)
    188, // ,
    189, // -
    190, // .
];

const contains = (array, item) => {
    return array.indexOf(item) >= 0;
};

export default class PostCodeFragment extends PureComponent {
    static propTypes = {
        className: PropTypes.oneOfType([PropTypes.object, PropTypes.string]),
        maxLength: PropTypes.number,
        onBlur: PropTypes.func.isRequired,
        onChange: PropTypes.func.isRequired,
        value: PropTypes.string,
        isReadonly: PropTypes.bool,
    };

    handleBlur = () => {
        const { onBlur } = this.props;
        const value = event.target.value;

        onBlur(value);
    };

    handleChange = event => {
        const { onChange } = this.props;
        const value = event.target.value;

        const fixedValue = value.replace(/\D/g,'');
        onChange(fixedValue);
    };

    handlePaste = event => {
        const pattern = new RegExp(`^\\d{0,${this.props.maxLength}}$`);
        const pasteData = event.clipboardData.getData('Text');
        if(!pattern.test(pasteData)) {
            event.preventDefault();
        }
    };

    handleKeyDown = event => {
        const functional = event.keyCode >= 112 && event.keyCode <= 123; // [F1] - [F12]
        const hotkeys =
            !event.altKey &&
            (contains(allowed, event.keyCode) ||
                (!event.shiftKey &&
                    contains(allowedWithoutShift, event.keyCode)) ||
                event.ctrlKey ||
                event.metaKey);
        let numerical;

        if (event.key && event.key !== 'Unidentified') {
            numerical = contains(allowedChars, event.key);
        } else {
            numerical =
                (!event.shiftKey &&
                    contains(allowedWithoutShiftChars, event.keyCode)) ||
                ((!event.shiftKey &&
                    (event.keyCode >= 48 && event.keyCode <= 57)) ||
                    (event.keyCode >= 96 && event.keyCode <= 105)); // [0] - [9], [Num0] - [Num9]
        }

        if (!functional && !hotkeys && !numerical) {
            event.preventDefault();
        }
    };

    render() {
        const { className, value, maxLength, isReadonly } = this.props;

        return (
            <input
                className={classNames(
                    'wfFormControl',
                    'form-control',
                    className
                )}
                onBlur={this.handleBlur}
                onChange={this.handleChange}
                onKeyDown={this.handleKeyDown}
                type="text"
                value={value}
                maxLength={maxLength}
                disabled={isReadonly}
                pattern="\d+"
                inputMode="numeric"
                onPaste={this.handlePaste}
            />
        );
    }
}
