using WebCon.WorkFlow.SDK.ConfigAttributes;

namespace WebCon.BpsExt.Training.CustomActions.Entities
{
    public class ValidationMessages
    {
        [ConfigEditableTranslation(DisplayName = "Not valid request", DefaultTranslation = "You can't request an amount of {0}")]
        public string NotValidRequestMessage { get; set; }
       
    }
}
