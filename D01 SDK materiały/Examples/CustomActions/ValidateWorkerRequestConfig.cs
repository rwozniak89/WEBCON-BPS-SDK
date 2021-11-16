using WebCon.WorkFlow.SDK.Common;
using WebCon.WorkFlow.SDK.ConfigAttributes;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class ValidateWorkerRequestConfig : PluginConfiguration
    {
        [ConfigEditableText(DisplayName = "Webservice URL", DefaultText = "http://srv38/sdktraining/api/erp/validate", IsRequired = true)]
        public string WebServiceUrl { get; set; }

        [ConfigEditableText(DisplayName = "Applying person", IsRequired = true)]
        public string Person { get; set; }

        [ConfigEditableText(DisplayName = "Requested amount", IsRequired = true)]
        public decimal Amount { get; set; }
    }
}