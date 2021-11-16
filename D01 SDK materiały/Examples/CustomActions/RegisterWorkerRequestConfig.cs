using WebCon.WorkFlow.SDK.Common;
using WebCon.WorkFlow.SDK.ConfigAttributes;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class RegisterWorkerRequestConfig : PluginConfiguration
    {
        [ConfigEditableText(DisplayName = "Webservice URL", DefaultText = "http://srv38/sdktraining/api/erp/register", IsRequired = true)]
        public string WebServiceUrl { get; set; }

        [ConfigEditableText(DisplayName = "Applying person", IsRequired = true)]
        public string Person { get; set; }

        [ConfigEditableText(DisplayName = "Requested amount", IsRequired = true)]
        public decimal Amount { get; set; }

        [ConfigEditableText(DisplayName = "Field with request ID", Description = "ID of the field with ID value from the ERP system", IsRequired = true)]
        public int FieldRequestID { get; set; }
    }
}