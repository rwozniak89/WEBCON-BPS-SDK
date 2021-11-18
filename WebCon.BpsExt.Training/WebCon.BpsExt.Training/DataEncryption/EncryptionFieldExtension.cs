using System;
using System.Text;
using WebCon.WorkFlow.SDK.Common.Model;
using WebCon.WorkFlow.SDK.FormFieldPlugins;

namespace WebCon.BpsExt.Training.DataEncryption
{
    public class EncryptionFieldExtension : FormFieldExtension<EncryptionFieldExtensionConfig>
    {
        public override object OnDBValueGet(object dbValue)
        {
            return  Encoding.ASCII.GetString(Convert.FromBase64String(dbValue.ToString()));  
        }

        public override object OnDBValueSet(object valueToSet)
        {
            return Convert.ToBase64String(Encoding.ASCII.GetBytes(valueToSet.ToString()));
        }
    }
}