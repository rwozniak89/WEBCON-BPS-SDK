using System;
using System.Collections.Generic;
using System.Data;
using System.Linq;
using WebCon.WorkFlow.SDK.Common.Model;
using WebCon.WorkFlow.SDK.FormFieldPlugins;
using WebCon.WorkFlow.SDK.FormFieldPlugins.Model;
using WebCon.WorkFlow.SDK.Tools.Data;
using WebCon.WorkFlow.SDK.Tools.Data.Model;

namespace WebCon.BpsExt.Training.TaxIdFormField
{
    public class TaxID : FormFieldExtension<TaxIDConfig, TaxIDValue>
    {
        public override TaxIDValue ConvertToControlType(object value)
        {
            var countryCodesDt = DataSourcesHelper.GetDataTableFromDataSource(new GetDataTableFromDataSourceParams(Configuration.CountryCodesDataSourceID, null, null));
            var countryCodesList = new List<string>();
            foreach (DataRow row in countryCodesDt.Rows)
                countryCodesList.Add(row.Field<string>(Configuration.CountryCodesColumnID));

            string countryCode = string.Empty, taxIdentificationNumber = string.Empty;
            if (!string.IsNullOrEmpty(value.ToString()) && value.ToString().Length > 2)

            {
                countryCode = value.ToString().Substring(0, 2);
                taxIdentificationNumber = value.ToString().Substring(2);
            }

            return new TaxIDValue()
            {
                CountryCodes = countryCodesList.ToArray(),
                CountryCode = countryCode,
                TaxIdentificationNumber = taxIdentificationNumber
            };
        }

        public override object ConvertToDBType(TaxIDValue value)
        {
            return string.Format("{0}{1}", value.CountryCode, value.TaxIdentificationNumber);

        }
              
    }
}
