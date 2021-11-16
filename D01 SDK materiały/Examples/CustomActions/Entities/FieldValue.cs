using WebCon.WorkFlow.SDK.ConfigAttributes;

namespace WebCon.BpsExt.Training.CustomActions.Entities
{
    public class FieldValue
    {
        [ConfigEditableGridColumnFormFieldID(DisplayName = "Filed ID")]
        public int FieldID { get; set; }

        [ConfigEditableGridColumn(DisplayName = "Value")]
        public string Value { get; set; }
    }
}
