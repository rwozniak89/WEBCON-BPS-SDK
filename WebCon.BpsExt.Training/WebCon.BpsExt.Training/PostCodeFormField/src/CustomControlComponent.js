import React, { PureComponent } from 'react';
import PropTypes from 'prop-types';
import PostCode from './components/PostCode';

// export default class CustomControlComponent extends PureComponent {
//     static propTypes = {
//         fieldConfiguration: PropTypes.shape({
//             displayName: PropTypes.string.isRequired,
//             description: PropTypes.string.isRequired,
//             isRequired: PropTypes.bool.isRequired,
//             editMode: PropTypes.oneOf([0, 1, 2]).isRequired,
//             isNew: PropTypes.bool.isRequired,
//             isAdmin: PropTypes.bool.isRequired,
//         }).isRequired,
//         model: PropTypes.any,
//         onChange: PropTypes.func.isRequired,
//         sdkConfiguration: PropTypes.object,
//     };

//     render() {
//         const {
//             fieldConfiguration,
//             model,
//             onChange,
//             sdkConfiguration,
//         } = this.props;

//         return <PostCode data={model} onChange={onChange} />;
//     }
// }

const CustomControlComponent = ({
    fieldConfiguration,
    model,
    onChange,
    sdkConfiguration,
}) => {
    if (
        fieldConfiguration.editMode === 'ReadOnlyHtml' &&
        !fieldConfiguration.isAdmin
    ) {
        return <span className="form-control-readonly">{model}</span>;
    } else {
        return (
            <PostCode
                data={model}
                onChange={onChange}
                fieldConfiguration={fieldConfiguration}
            />
        );
    }
};

CustomControlComponent.propTypes = {
    fieldConfiguration: PropTypes.shape({
        displayName: PropTypes.string.isRequired,
        description: PropTypes.string.isRequired,
        isRequired: PropTypes.bool.isRequired,
        editMode: PropTypes.oneOf(['Edit', 'ReadOnly', 'ReadOnlyHtml'])
            .isRequired,
        isNew: PropTypes.bool.isRequired,
        isAdmin: PropTypes.bool.isRequired,
    }).isRequired,
    model: PropTypes.any,
    onChange: PropTypes.func.isRequired,
    sdkConfiguration: PropTypes.object,
};

export default CustomControlComponent;
