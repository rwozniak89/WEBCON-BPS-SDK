using WebCon.WorkFlow.SDK.Common;
using WebCon.WorkFlow.SDK.ConfigAttributes;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class RegisterWorkerRequestConfig : PluginConfiguration
    {
        //[ConfigEditableText(DisplayName = "Webservice URL", DefaultText = "http://srv38/sdktraining/api/erp/register", IsRequired = true)]
        //public string WebServiceUrl { get; set; }

        [ConfigEditableConnectionID("ERP webServices", IsRequired = true, ConnectionsType = DataConnectionType.WebServiceREST)]
        public int ConnectionID { get; set; }

        [ConfigEditableText(DisplayName = "Endpoint", DefaultText = "api/erp/register", IsRequired = true)]
        public string EndpointUrl { get; set; }

        [ConfigEditableText(DisplayName = "Applying person", IsRequired = true)]
        public string Person { get; set; }

        [ConfigEditableText(DisplayName = "Requested amount", IsRequired = true)]
        public decimal Amount { get; set; }

        [ConfigEditableFormFieldID(DisplayName = "Field with request ID", Description = "ID of the field with ID value from the ERP system", IsRequired = true
            , FormFieldTypes = FormFieldTypes.Integer | FormFieldTypes.Decimal)]
        public int FieldRequestID { get; set; }
    }
}