import React, { PureComponent } from 'react';
import PropTypes from 'prop-types';
import PostCodeFragment from './PostCodeFragment';

import './PostCode.css';

const createState = data => {
    const result = /^([0-9]{0,2})-{1}([0-9]{0,3})$/gi.exec(data);

    if (result) {
        return {
            fragment1: result[1],
            fragment2: result[2],
            prevData: data,
        };
    } else {
        return {
            fragment1: '',
            fragment2: '',
            prevData: data,
        };
    }
};

export default class PostCode extends PureComponent {
    state = createState(this.props.data);

    static propTypes = {
        data: PropTypes.string.isRequired,
        onChange: PropTypes.func.isRequired,
        fieldConfiguration: PropTypes.object.isRequired,
    };

    static getDerivedStateFromProps(props, state) {
        if (props.data !== state.prevData) {
            return createState(props.data);
        }

        return null;
    }

    handleBlur = () => {
        const { onChange } = this.props;
        const { fragment1, fragment2, prevData } = this.state;

        const data = fragment1 || fragment2 ? `${fragment1}-${fragment2}` : '';

        if (data !== prevData) {
            const result = /^([0-9]{0,2})-{1}([0-9]{0,3})$/gi.exec(data);

            if (result) {
                onChange(data);
            } else {
                onChange('');
            }
        }
    };

    handleChangeFragment1 = value => {
        this.setState({ fragment1: value });
    };

    handleChangeFragment2 = value => {
        this.setState({ fragment2: value });
    };

    handleClick = () => {
        const { onChange } = this.props;
        const { fragment1, fragment2 } = this.state;

        if (fragment1 || fragment2) {
            onChange('');
        }
    };

    render() {
        const fieldConfiguration = this.props.fieldConfiguration;
        const isDisabled = fieldConfiguration.isDisabled;
        const isAdmin = fieldConfiguration.isAdmin;
        const isReadonly = isDisabled && !isAdmin;

        return (
            <div>
                <PostCodeFragment
                    className="post-code--fragment"
                    maxLength={2}
                    onBlur={this.handleBlur}
                    onChange={this.handleChangeFragment1}
                    value={this.state.fragment1}
                    isReadonly={isReadonly}
                />
                <span className="post-code--separator">-</span>
                <PostCodeFragment
                    className="post-code--fragment post-code--fragment__second"
                    maxLength={3}
                    onBlur={this.handleBlur}
                    onChange={this.handleChangeFragment2}
                    value={this.state.fragment2}
                    isReadonly={isReadonly}
                />
                {!isReadonly && (
                    <button
                        className="post-code--clear-btn"
                        type="button"
                        onClick={this.handleClick}
                    >
                        <img className="clear-btn--image" src="assets/clear" />
                    </button>
                )}
            </div>
        );
    }
}
