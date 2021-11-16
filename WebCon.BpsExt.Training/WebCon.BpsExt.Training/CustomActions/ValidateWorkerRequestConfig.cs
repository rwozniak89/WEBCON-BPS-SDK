using WebCon.WorkFlow.SDK.Common;
using WebCon.WorkFlow.SDK.ConfigAttributes;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class ValidateWorkerRequestConfig : PluginConfiguration
    {
        [ConfigEditableText(DisplayName = "Webservice URL", DefaultText = "http://srv38/sdktraining/api/erp/validate", IsRequired = true, Multiline = true, Lines = 3,
            TagEvaluationMode = EvaluationMode.SQL)]
        public string WebServiceUrl { get; set; }

        [ConfigEditableText(DisplayName = "Applying person", IsRequired = true)]
        public string Person { get; set; }

        [ConfigEditableText(DisplayName = "Requested amount", IsRequired = true, NullText = "500")]
        public decimal Amount { get; set; }

        [ConfigEditableTranslationsList("Exception messages", AdditionalCultures = "en")]
        public ValidationMessages ValidationMessages { get; set; }

        [ConfigEditableConnectionID("Poł do serwisu")]
        public int? ConnectionID { get; set; }
    }

    public class ValidationMessages
    {
        [ConfigEditableTranslation ("Invalid request", DefaultTranslation = "You can't request an amount of {0}", Description = "{0} = ammount")]
        public string InvalidRequestMessage { get; set; }
    }
}