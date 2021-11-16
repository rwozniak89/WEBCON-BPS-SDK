using WebCon.WorkFlow.SDK.Common;
using WebCon.WorkFlow.SDK.ConfigAttributes;

namespace WebCon.BpsExt.Training.CustomBusinessRules
{
    public class ValidateSuperiorConfig : PluginConfiguration
    {
        [ConfigEditableDataSourceID(DisplayName = "Managers", Description = "Data sources that return managers who can approve requests")]
        public int SuperiorsDataSourceID { get; set; }

        [ConfigEditableText(DisplayName = "Selected manager", Description = "Data of the currently selected manager")]
        public string CurrentSuperior { get; set; }
    }
}