using Newtonsoft.Json;
using System.Net.Http;
using System.Text;
using WebCon.WorkFlow.SDK.ActionPlugins;
using WebCon.WorkFlow.SDK.ActionPlugins.Model;

namespace WebCon.BpsExt.Training.CustomActions
{
    public class ValidateWorkerRequest : CustomAction<ValidateWorkerRequestConfig>
    {
        public override void Run(RunCustomActionParams args)
        {
                      
            if (!IsRequestValid(new RequestData(Configuration.Person, Configuration.Amount)))
            {
                args.HasErrors = true;
                args.Message = string.Format("You can't request an amount of {0}", Configuration.Amount);
            }
        }

        private bool IsRequestValid(RequestData requestData)
        {
            return CallERPService<bool>(Configuration.WebServiceUrl, requestData);
        }

        private T CallERPService<T>(string url, RequestData data)
        {
            string jsonRequest = JsonConvert.SerializeObject(data);
            var content = new StringContent(jsonRequest, Encoding.UTF8, "application/json");

            var client = new HttpClient();
            var response = client.PostAsync(url, content).Result;
            response.EnsureSuccessStatusCode();
            var result = response.Content.ReadAsStringAsync().Result;
            T jsonResult = JsonConvert.DeserializeObject<T>(result);
            return jsonResult;
        }

        public class RequestData
        {
            public string bpsId { get; set; }
            public decimal amount { get; set; }

            public RequestData(string bpsId, decimal amount)
            {
                this.bpsId = bpsId;
                this.amount = amount;
            }
        }
    }
}