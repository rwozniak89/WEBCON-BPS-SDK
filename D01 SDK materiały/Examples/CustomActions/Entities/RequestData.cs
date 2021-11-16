using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace WebCon.BpsExt.Training.CustomActions.Entities
{
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
