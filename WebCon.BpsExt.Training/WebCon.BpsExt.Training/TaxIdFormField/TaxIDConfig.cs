using WebCon.WorkFlow.SDK.Common;
using WebCon.WorkFlow.SDK.ConfigAttributes;

namespace WebCon.BpsExt.Training.TaxIdFormField
{
    public class TaxIDConfig : PluginConfiguration
    {
        [ConfigEditableDataSourceID(DisplayName = "Countries DataSource", IsRequired = true)]
        public int CountryCodesDataSourceID { get; set; }

        [ConfigEditableText(DisplayName = "Column of country ID")]
        public string CountryCodesColumnID { get; set; }

        [ConfigEditableText(DisplayName = "Column of country name")]
        public string CountryCodesColumnName { get; set; }
    }
}
