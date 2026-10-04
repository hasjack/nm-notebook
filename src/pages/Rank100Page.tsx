import { Link } from "react-router-dom";

const FLOORS: {
  k: number;
  eps: string;
  expr: string;
  factor: string;
  seconds: string;
}[] = [
  { k: 98, eps: "−1", expr: "224714·2^n−99", factor: "162981019", seconds: "1,234" },
  { k: 100, eps: "+1", expr: "229300·2^n−99", factor: "393061223", seconds: "2,896" },
  { k: 104, eps: "−1", expr: "238472·2^n−105", factor: "(none stored)", seconds: "0.28" },
  { k: 106, eps: "+1", expr: "243058·2^n−105", factor: "212669", seconds: "2.96" },
  { k: 110, eps: "−1", expr: "252230·2^n−111", factor: "17", seconds: "0.31" },
  { k: 112, eps: "+1", expr: "256816·2^n−111", factor: "13", seconds: "0.27" },
  { k: 116, eps: "−1", expr: "265988·2^n−117", factor: "43242769", seconds: "360" },
  { k: 118, eps: "+1", expr: "270574·2^n−117", factor: "5", seconds: "0.27" },
  { k: 122, eps: "−1", expr: "279746·2^n−123", factor: "5", seconds: "0.27" },
  { k: 124, eps: "+1", expr: "284332·2^n−123", factor: "Fermat composite", seconds: "25.69 h" },
  { k: 128, eps: "−1", expr: "293504·2^n−129", factor: "67", seconds: "0.28" },
  { k: 130, eps: "+1", expr: "298090·2^n−129", factor: "23", seconds: "0.28" },
  { k: 134, eps: "−1", expr: "307262·2^n−135", factor: "7", seconds: "0.28" },
  { k: 136, eps: "+1", expr: "311848·2^n−135", factor: "439", seconds: "0.29" },
  { k: 140, eps: "−1", expr: "321020·2^n−141", factor: "37", seconds: "0.28" },
  { k: 142, eps: "+1", expr: "325606·2^n−141", factor: "Fermat composite", seconds: "24.96 h" },
  { k: 146, eps: "−1", expr: "334778·2^n−147", factor: "23", seconds: "0.28" },
  { k: 148, eps: "+1", expr: "339364·2^n−147", factor: "(none stored)", seconds: "0.27" },
  { k: 152, eps: "−1", expr: "348536·2^n−153", factor: "(none stored)", seconds: "0.28" },
  { k: 154, eps: "+1", expr: "353122·2^n−153", factor: "79", seconds: "0.32" },
  { k: 158, eps: "−1", expr: "362294·2^n−159", factor: "61", seconds: "0.32" },
  { k: 160, eps: "+1", expr: "366880·2^n−159", factor: "7", seconds: "0.27" },
  { k: 164, eps: "−1", expr: "376052·2^n−165", factor: "59", seconds: "0.27" },
  { k: 166, eps: "+1", expr: "380638·2^n−165", factor: "19", seconds: "0.28" },
  { k: 170, eps: "−1", expr: "389810·2^n−171", factor: "11", seconds: "0.27" },
  { k: 172, eps: "+1", expr: "394396·2^n−171", factor: "41", seconds: "0.28" },
  { k: 176, eps: "−1", expr: "403568·2^n−177", factor: "7", seconds: "0.28" },
  { k: 178, eps: "+1", expr: "408154·2^n−177", factor: "5", seconds: "0.28" },
  { k: 182, eps: "−1", expr: "417326·2^n−183", factor: "5", seconds: "0.28" },
  { k: 184, eps: "+1", expr: "421912·2^n−183", factor: "373", seconds: "0.28" },
  { k: 188, eps: "−1", expr: "431084·2^n−189", factor: "Fermat composite", seconds: "25.02 h" },
  { k: 190, eps: "+1", expr: "435670·2^n−189", factor: "13", seconds: "0.28" },
  { k: 194, eps: "−1", expr: "444842·2^n−195", factor: "293", seconds: "0.29" },
  { k: 196, eps: "+1", expr: "449428·2^n−195", factor: "17", seconds: "0.28" },
  { k: 200, eps: "−1", expr: "458600·2^n−201", factor: "13", seconds: "0.27" },
  { k: 202, eps: "+1", expr: "463186·2^n−201", factor: "7", seconds: "0.28" },
  { k: 206, eps: "−1", expr: "472358·2^n−207", factor: "Fermat composite", seconds: "24.34 h" },
  { k: 208, eps: "+1", expr: "476944·2^n−207", factor: "5", seconds: "0.32" },
  { k: 212, eps: "−1", expr: "486116·2^n−213", factor: "5", seconds: "0.31" },
  { k: 214, eps: "+1", expr: "490702·2^n−213", factor: "Fermat composite", seconds: "24.66 h" },
  { k: 218, eps: "−1", expr: "499874·2^n−219", factor: "7", seconds: "0.27" },
  { k: 220, eps: "+1", expr: "504460·2^n−219", factor: "18481", seconds: "0.55" },
  { k: 224, eps: "−1", expr: "513632·2^n−225", factor: "641", seconds: "0.31" },
  { k: 226, eps: "+1", expr: "518218·2^n−225", factor: "11", seconds: "0.33" },
  { k: 230, eps: "−1", expr: "527390·2^n−231", factor: "127891349", seconds: "970" },
  { k: 232, eps: "+1", expr: "531976·2^n−231", factor: "269", seconds: "0.28" },
  { k: 236, eps: "−1", expr: "541148·2^n−237", factor: "11", seconds: "0.27" },
  { k: 238, eps: "+1", expr: "545734·2^n−237", factor: "5", seconds: "0.28" },
  { k: 242, eps: "−1", expr: "554906·2^n−243", factor: "5", seconds: "0.28" },
  { k: 244, eps: "+1", expr: "559492·2^n−243", factor: "7", seconds: "0.28" },
  { k: 248, eps: "−1", expr: "568664·2^n−249", factor: "479", seconds: "0.28" },
  { k: 250, eps: "+1", expr: "573250·2^n−249", factor: "43", seconds: "0.28" },
  { k: 254, eps: "−1", expr: "582422·2^n−255", factor: "28433", seconds: "0.7" },
  { k: 256, eps: "+1", expr: "587008·2^n−255", factor: "32003", seconds: "0.74" },
  { k: 260, eps: "−1", expr: "596180·2^n−261", factor: "(none stored)", seconds: "0.28" },
  { k: 262, eps: "+1", expr: "600766·2^n−261", factor: "105499", seconds: "1.57" },
  { k: 266, eps: "−1", expr: "609938·2^n−267", factor: "43", seconds: "0.27" },
  { k: 268, eps: "+1", expr: "614524·2^n−267", factor: "5", seconds: "0.29" },
  { k: 272, eps: "−1", expr: "623696·2^n−273", factor: "5", seconds: "0.27" },
  { k: 274, eps: "+1", expr: "628282·2^n−273", factor: "67", seconds: "0.28" },
  { k: 278, eps: "−1", expr: "637454·2^n−279", factor: "13", seconds: "0.27" },
  { k: 280, eps: "+1", expr: "642040·2^n−279", factor: "19", seconds: "0.27" },
  { k: 284, eps: "−1", expr: "651212·2^n−285", factor: "23", seconds: "0.28" },
  { k: 286, eps: "+1", expr: "655798·2^n−285", factor: "7", seconds: "0.27" },
  { k: 290, eps: "−1", expr: "664970·2^n−291", factor: "19", seconds: "0.27" },
  { k: 292, eps: "+1", expr: "669556·2^n−291", factor: "11", seconds: "0.27" },
  { k: 296, eps: "−1", expr: "678728·2^n−297", factor: "14146369", seconds: "124" },
  { k: 298, eps: "+1", expr: "683314·2^n−297", factor: "(none stored)", seconds: "0.27" },
  { k: 302, eps: "−1", expr: "692486·2^n−303", factor: "(none stored)", seconds: "0.27" },
  { k: 304, eps: "+1", expr: "697072·2^n−303", factor: "37", seconds: "0.27" },
  { k: 308, eps: "−1", expr: "706244·2^n−309", factor: "2437", seconds: "0.3" },
  { k: 310, eps: "+1", expr: "710830·2^n−309", factor: "3083", seconds: "0.33" },
  { k: 314, eps: "−1", expr: "720002·2^n−315", factor: "17", seconds: "0.27" },
  { k: 316, eps: "+1", expr: "724588·2^n−315", factor: "2161", seconds: "0.31" },
  { k: 320, eps: "−1", expr: "733760·2^n−321", factor: "31", seconds: "0.27" },
  { k: 322, eps: "+1", expr: "738346·2^n−321", factor: "4723", seconds: "0.34" },
  { k: 326, eps: "−1", expr: "747518·2^n−327", factor: "Fermat composite", seconds: "24.85 h" },
  { k: 328, eps: "+1", expr: "752104·2^n−327", factor: "5", seconds: "0.27" },
  { k: 332, eps: "−1", expr: "761276·2^n−333", factor: "5", seconds: "0.27" },
  { k: 334, eps: "+1", expr: "765862·2^n−333", factor: "103", seconds: "0.32" },
  { k: 338, eps: "−1", expr: "775034·2^n−339", factor: "53", seconds: "0.32" },
  { k: 340, eps: "+1", expr: "779620·2^n−339", factor: "643", seconds: "0.28" },
  { k: 344, eps: "−1", expr: "788792·2^n−345", factor: "7", seconds: "0.27" },
  { k: 346, eps: "+1", expr: "793378·2^n−345", factor: "13", seconds: "0.27" },
  { k: 350, eps: "−1", expr: "802550·2^n−351", factor: "83", seconds: "0.27" },
  { k: 352, eps: "+1", expr: "807136·2^n−351", factor: "251", seconds: "0.28" },
  { k: 356, eps: "−1", expr: "816308·2^n−357", factor: "13", seconds: "0.27" },
  { k: 358, eps: "+1", expr: "820894·2^n−357", factor: "5", seconds: "0.27" },
  { k: 362, eps: "−1", expr: "830066·2^n−363", factor: "5", seconds: "0.27" },
  { k: 364, eps: "+1", expr: "834652·2^n−363", factor: "8101", seconds: "0.4" },
  { k: 368, eps: "−1", expr: "843824·2^n−369", factor: "11", seconds: "0.28" },
  { k: 370, eps: "+1", expr: "848410·2^n−369", factor: "7", seconds: "0.35" },
  { k: 374, eps: "−1", expr: "857582·2^n−375", factor: "1373", seconds: "0.4" },
  { k: 376, eps: "+1", expr: "862168·2^n−375", factor: "941", seconds: "0.39" },
  { k: 380, eps: "−1", expr: "871340·2^n−381", factor: "337", seconds: "0.38" },
  { k: 382, eps: "+1", expr: "875926·2^n−381", factor: "5081", seconds: "0.44" },
  { k: 386, eps: "−1", expr: "885098·2^n−387", factor: "7", seconds: "0.33" },
  { k: 388, eps: "+1", expr: "889684·2^n−387", factor: "5", seconds: "0.38" },
  { k: 392, eps: "−1", expr: "898856·2^n−393", factor: "5", seconds: "0.35" },
  { k: 394, eps: "+1", expr: "903442·2^n−393", factor: "19", seconds: "0.34" },
  { k: 398, eps: "−1", expr: "912614·2^n−399", factor: "30773", seconds: "0.79" },
  { k: 400, eps: "+1", expr: "917200·2^n−399", factor: "17", seconds: "0.31" },
  { k: 404, eps: "−1", expr: "926372·2^n−405", factor: "19", seconds: "0.3" },
  { k: 406, eps: "+1", expr: "930958·2^n−405", factor: "23", seconds: "0.28" },
  { k: 410, eps: "−1", expr: "940130·2^n−411", factor: "6397", seconds: "0.37" },
  { k: 412, eps: "+1", expr: "944716·2^n−411", factor: "7", seconds: "0.27" },
  { k: 416, eps: "−1", expr: "953888·2^n−417", factor: "17", seconds: "0.27" },
  { k: 418, eps: "+1", expr: "958474·2^n−417", factor: "5", seconds: "0.26" },
  { k: 422, eps: "−1", expr: "967646·2^n−423", factor: "5", seconds: "0.26" },
  { k: 424, eps: "+1", expr: "972232·2^n−423", factor: "11", seconds: "0.27" },
  { k: 428, eps: "−1", expr: "981404·2^n−429", factor: "7", seconds: "0.27" },
  { k: 430, eps: "+1", expr: "985990·2^n−429", factor: "47", seconds: "0.27" },
  { k: 434, eps: "−1", expr: "995162·2^n−435", factor: "11", seconds: "0.26" },
  { k: 436, eps: "+1", expr: "999748·2^n−435", factor: "2969", seconds: "0.32" },
  { k: 440, eps: "−1", expr: "1008920·2^n−441", factor: "457", seconds: "0.28" },
  { k: 442, eps: "+1", expr: "1013506·2^n−441", factor: "Fermat composite", seconds: "25.17 h" },
  { k: 446, eps: "−1", expr: "1022678·2^n−447", factor: "389", seconds: "0.28" },
  { k: 448, eps: "+1", expr: "1027264·2^n−447", factor: "(none stored)", seconds: "0.28" },
  { k: 452, eps: "−1", expr: "1036436·2^n−453", factor: "(none stored)", seconds: "0.34" },
  { k: 454, eps: "+1", expr: "1041022·2^n−453", factor: "7", seconds: "0.33" },
  { k: 458, eps: "−1", expr: "1050194·2^n−459", factor: "29", seconds: "0.33" },
  { k: 460, eps: "+1", expr: "1054780·2^n−459", factor: "5683", seconds: "0.46" },
  { k: 464, eps: "−1", expr: "1063952·2^n−465", factor: "211", seconds: "0.38" },
  { k: 466, eps: "+1", expr: "1068538·2^n−465", factor: "4889", seconds: "0.53" },
  { k: 470, eps: "−1", expr: "1077710·2^n−471", factor: "7", seconds: "0.32" },
  { k: 472, eps: "+1", expr: "1082296·2^n−471", factor: "Fermat composite", seconds: "25.09 h" },
  { k: 476, eps: "−1", expr: "1091468·2^n−477", factor: "1433", seconds: "0.34" },
  { k: 478, eps: "+1", expr: "1096054·2^n−477", factor: "5", seconds: "0.32" },
  { k: 482, eps: "−1", expr: "1105226·2^n−483", factor: "5", seconds: "0.32" },
  { k: 484, eps: "+1", expr: "1109812·2^n−483", factor: "73", seconds: "0.35" },
  { k: 488, eps: "−1", expr: "1118984·2^n−489", factor: "28661", seconds: "0.85" },
  { k: 490, eps: "+1", expr: "1123570·2^n−489", factor: "11", seconds: "0.32" },
  { k: 494, eps: "−1", expr: "1132742·2^n−495", factor: "193", seconds: "0.33" },
  { k: 496, eps: "+1", expr: "1137328·2^n−495", factor: "7", seconds: "0.34" },
  { k: 500, eps: "−1", expr: "1146500·2^n−501", factor: "11", seconds: "0.33" },
  { k: 502, eps: "+1", expr: "1151086·2^n−501", factor: "13", seconds: "0.34" },
  { k: 506, eps: "−1", expr: "1160258·2^n−507", factor: "31", seconds: "0.32" },
  { k: 508, eps: "+1", expr: "1164844·2^n−507", factor: "5", seconds: "0.32" },
  { k: 512, eps: "−1", expr: "1174016·2^n−513", factor: "5", seconds: "0.28" },
  { k: 514, eps: "+1", expr: "1178602·2^n−513", factor: "4987", seconds: "0.36" },
  { k: 518, eps: "−1", expr: "1187774·2^n−519", factor: "17", seconds: "0.27" },
  { k: 520, eps: "+1", expr: "1192360·2^n−519", factor: "4729", seconds: "0.35" },
  { k: 524, eps: "−1", expr: "1201532·2^n−525", factor: "43", seconds: "0.27" },
  { k: 526, eps: "+1", expr: "1206118·2^n−525", factor: "37", seconds: "0.27" },
  { k: 530, eps: "−1", expr: "1215290·2^n−531", factor: "67", seconds: "0.28" },
  { k: 532, eps: "+1", expr: "1219876·2^n−531", factor: "803087", seconds: "8.93" },
  { k: 536, eps: "−1", expr: "1229048·2^n−537", factor: "4021", seconds: "0.34" },
  { k: 538, eps: "+1", expr: "1233634·2^n−537", factor: "5", seconds: "0.27" },
  { k: 542, eps: "−1", expr: "1242806·2^n−543", factor: "5", seconds: "0.27" },
  { k: 544, eps: "+1", expr: "1247392·2^n−543", factor: "23", seconds: "0.27" },
  { k: 548, eps: "−1", expr: "1256564·2^n−549", factor: "277", seconds: "0.28" },
  { k: 550, eps: "+1", expr: "1261150·2^n−549", factor: "5408981", seconds: "50.1" },
  { k: 554, eps: "−1", expr: "1270322·2^n−555", factor: "(none stored)", seconds: "0.27" },
  { k: 556, eps: "+1", expr: "1274908·2^n−555", factor: "11", seconds: "0.27" },
  { k: 560, eps: "−1", expr: "1284080·2^n−561", factor: "23", seconds: "0.27" },
  { k: 562, eps: "+1", expr: "1288666·2^n−561", factor: "2758891", seconds: "26.6" },
  { k: 566, eps: "−1", expr: "1297838·2^n−567", factor: "11", seconds: "0.27" },
  { k: 568, eps: "+1", expr: "1302424·2^n−567", factor: "5", seconds: "0.27" },
  { k: 572, eps: "−1", expr: "1311596·2^n−573", factor: "5", seconds: "0.27" },
  { k: 574, eps: "+1", expr: "1316182·2^n−573", factor: "61", seconds: "0.27" },
  { k: 578, eps: "−1", expr: "1325354·2^n−579", factor: "4260049", seconds: "40.9" },
  { k: 580, eps: "+1", expr: "1329940·2^n−579", factor: "7", seconds: "0.27" },
  { k: 584, eps: "−1", expr: "1339112·2^n−585", factor: "37", seconds: "0.28" },
  { k: 586, eps: "+1", expr: "1343698·2^n−585", factor: "29", seconds: "0.27" },
  { k: 590, eps: "−1", expr: "1352870·2^n−591", factor: "13", seconds: "0.27" },
  { k: 592, eps: "+1", expr: "1357456·2^n−591", factor: "113", seconds: "0.28" },
  { k: 596, eps: "−1", expr: "1366628·2^n−597", factor: "7", seconds: "0.27" },
  { k: 598, eps: "+1", expr: "1371214·2^n−597", factor: "(none stored)", seconds: "0.28" },
  { k: 602, eps: "−1", expr: "1380386·2^n−603", factor: "(none stored)", seconds: "0.28" },
  { k: 604, eps: "+1", expr: "1384972·2^n−603", factor: "17", seconds: "0.28" },
  { k: 608, eps: "−1", expr: "1394144·2^n−609", factor: "107", seconds: "0.28" },
  { k: 610, eps: "+1", expr: "1398730·2^n−609", factor: "31", seconds: "0.28" },
  { k: 614, eps: "−1", expr: "1407902·2^n−615", factor: "1254557", seconds: "13.3" },
  { k: 616, eps: "+1", expr: "1412488·2^n−615", factor: "(none stored)", seconds: "0.33" },
  { k: 620, eps: "−1", expr: "1421660·2^n−621", factor: "(none stored)", seconds: "0.32" },
  { k: 622, eps: "+1", expr: "1426246·2^n−621", factor: "(none stored)", seconds: "0.34" },
  { k: 626, eps: "−1", expr: "1435418·2^n−627", factor: "Fermat composite", seconds: "25.71 h" },
  { k: 628, eps: "+1", expr: "1440004·2^n−627", factor: "5", seconds: "0.34" },
  { k: 632, eps: "−1", expr: "1449176·2^n−633", factor: "5", seconds: "0.32" },
  { k: 634, eps: "+1", expr: "1453762·2^n−633", factor: "10086859", seconds: "91.5" },
  { k: 638, eps: "−1", expr: "1462934·2^n−639", factor: "7", seconds: "0.28" },
  { k: 640, eps: "+1", expr: "1467520·2^n−639", factor: "690323", seconds: "8.42" },
  { k: 644, eps: "−1", expr: "1476692·2^n−645", factor: "241", seconds: "0.3" },
  { k: 646, eps: "+1", expr: "1481278·2^n−645", factor: "83", seconds: "0.31" },
  { k: 650, eps: "−1", expr: "1490450·2^n−651", factor: "6922457", seconds: "64.2" },
  { k: 652, eps: "+1", expr: "1495036·2^n−651", factor: "101", seconds: "0.32" },
  { k: 656, eps: "−1", expr: "1504208·2^n−657", factor: "53", seconds: "0.33" },
  { k: 658, eps: "+1", expr: "1508794·2^n−657", factor: "5", seconds: "0.32" },
  { k: 662, eps: "−1", expr: "1517966·2^n−663", factor: "5", seconds: "0.31" },
  { k: 664, eps: "+1", expr: "1522552·2^n−663", factor: "7", seconds: "0.32" },
  { k: 668, eps: "−1", expr: "1531724·2^n−669", factor: "13", seconds: "0.3" },
  { k: 670, eps: "+1", expr: "1536310·2^n−669", factor: "7691", seconds: "0.48" },
  { k: 674, eps: "−1", expr: "1545482·2^n−675", factor: "692513", seconds: "8.15" },
  { k: 676, eps: "+1", expr: "1550068·2^n−675", factor: "67", seconds: "0.31" },
  { k: 680, eps: "−1", expr: "1559240·2^n−681", factor: "7", seconds: "0.27" },
  { k: 682, eps: "+1", expr: "1563826·2^n−681", factor: "23", seconds: "0.33" },
  { k: 686, eps: "−1", expr: "1572998·2^n−687", factor: "3217", seconds: "0.47" },
  { k: 688, eps: "+1", expr: "1577584·2^n−687", factor: "5", seconds: "0.38" },
  { k: 692, eps: "−1", expr: "1586756·2^n−693", factor: "5", seconds: "0.29" },
  { k: 694, eps: "+1", expr: "1591342·2^n−693", factor: "10631", seconds: "0.49" },
  { k: 698, eps: "−1", expr: "1600514·2^n−699", factor: "11", seconds: "0.28" },
  { k: 700, eps: "+1", expr: "1605100·2^n−699", factor: "1108703", seconds: "11.8" },
  { k: 704, eps: "−1", expr: "1614272·2^n−705", factor: "Fermat composite", seconds: "25.71 h" },
  { k: 706, eps: "+1", expr: "1618858·2^n−705", factor: "7", seconds: "0.28" },
  { k: 710, eps: "−1", expr: "1628030·2^n−711", factor: "233", seconds: "0.28" },
  { k: 712, eps: "+1", expr: "1632616·2^n−711", factor: "47", seconds: "0.28" },
  { k: 716, eps: "−1", expr: "1641788·2^n−717", factor: "Fermat composite", seconds: "25.51 h" },
  { k: 718, eps: "+1", expr: "1646374·2^n−717", factor: "5", seconds: "0.27" },
  { k: 722, eps: "−1", expr: "1655546·2^n−723", factor: "5", seconds: "0.27" },
  { k: 724, eps: "+1", expr: "1660132·2^n−723", factor: "169667", seconds: "2.26" },
  { k: 728, eps: "−1", expr: "1669304·2^n−729", factor: "599", seconds: "0.29" },
  { k: 730, eps: "+1", expr: "1673890·2^n−729", factor: "2789", seconds: "0.32" },
  { k: 734, eps: "−1", expr: "1683062·2^n−735", factor: "97", seconds: "0.27" },
  { k: 736, eps: "+1", expr: "1687648·2^n−735", factor: "13", seconds: "0.27" },
  { k: 740, eps: "−1", expr: "1696820·2^n−741", factor: "409", seconds: "0.28" },
  { k: 742, eps: "+1", expr: "1701406·2^n−741", factor: "2193383", seconds: "22.2" },
  { k: 746, eps: "−1", expr: "1710578·2^n−747", factor: "13", seconds: "0.27" },
  { k: 748, eps: "+1", expr: "1715164·2^n−747", factor: "(none stored)", seconds: "0.27" },
  { k: 752, eps: "−1", expr: "1724336·2^n−753", factor: "(none stored)", seconds: "0.28" },
  { k: 754, eps: "+1", expr: "1728922·2^n−753", factor: "11", seconds: "0.3" },
  { k: 758, eps: "−1", expr: "1738094·2^n−759", factor: "5737583", seconds: "53.3" },
  { k: 760, eps: "+1", expr: "1742680·2^n−759", factor: "29", seconds: "0.33" },
  { k: 764, eps: "−1", expr: "1751852·2^n−765", factor: "7", seconds: "0.31" },
  { k: 766, eps: "+1", expr: "1756438·2^n−765", factor: "43", seconds: "0.31" },
  { k: 770, eps: "−1", expr: "1765610·2^n−771", factor: "197", seconds: "0.33" },
  { k: 772, eps: "+1", expr: "1770196·2^n−771", factor: "2851", seconds: "0.39" },
  { k: 776, eps: "−1", expr: "1779368·2^n−777", factor: "3593", seconds: "0.41" },
  { k: 778, eps: "+1", expr: "1783954·2^n−777", factor: "5", seconds: "0.36" },
  { k: 782, eps: "−1", expr: "1793126·2^n−783", factor: "5", seconds: "0.32" },
  { k: 784, eps: "+1", expr: "1797712·2^n−783", factor: "62323", seconds: "1.17" },
  { k: 788, eps: "−1", expr: "1806884·2^n−789", factor: "37463", seconds: "0.89" },
  { k: 790, eps: "+1", expr: "1811470·2^n−789", factor: "7", seconds: "0.32" },
  { k: 794, eps: "−1", expr: "1820642·2^n−795", factor: "79", seconds: "0.29" },
  { k: 796, eps: "+1", expr: "1825228·2^n−795", factor: "31", seconds: "0.28" },
  { k: 800, eps: "−1", expr: "1834400·2^n−801", factor: "5569", seconds: "0.39" },
  { k: 802, eps: "+1", expr: "1838986·2^n−801", factor: "211", seconds: "0.28" },
  { k: 806, eps: "−1", expr: "1848158·2^n−807", factor: "7", seconds: "0.28" },
  { k: 808, eps: "+1", expr: "1852744·2^n−807", factor: "5", seconds: "0.28" },
  { k: 812, eps: "−1", expr: "1861916·2^n−813", factor: "5", seconds: "0.28" },
  { k: 814, eps: "+1", expr: "1866502·2^n−813", factor: "13", seconds: "0.28" },
  { k: 818, eps: "−1", expr: "1875674·2^n−819", factor: "3457", seconds: "0.34" },
  { k: 820, eps: "+1", expr: "1880260·2^n−819", factor: "11", seconds: "0.29" },
  { k: 824, eps: "−1", expr: "1889432·2^n−825", factor: "13", seconds: "0.33" },
  { k: 826, eps: "+1", expr: "1894018·2^n−825", factor: "71", seconds: "0.33" },
  { k: 830, eps: "−1", expr: "1903190·2^n−831", factor: "(none stored)", seconds: "0.3" },
  { k: 832, eps: "+1", expr: "1907776·2^n−831", factor: "7", seconds: "0.3" },
  { k: 836, eps: "−1", expr: "1916948·2^n−837", factor: "23", seconds: "0.28" },
  { k: 838, eps: "+1", expr: "1921534·2^n−837", factor: "5", seconds: "0.28" },
  { k: 842, eps: "−1", expr: "1930706·2^n−843", factor: "5", seconds: "0.27" },
  { k: 844, eps: "+1", expr: "1935292·2^n−843", factor: "1097237", seconds: "11.8" },
  { k: 848, eps: "−1", expr: "1944464·2^n−849", factor: "(none stored)", seconds: "0.27" },
  { k: 850, eps: "+1", expr: "1949050·2^n−849", factor: "19", seconds: "0.27" },
  { k: 854, eps: "−1", expr: "1958222·2^n−855", factor: "2683", seconds: "0.33" },
  { k: 856, eps: "+1", expr: "1962808·2^n−855", factor: "839", seconds: "0.3" },
  { k: 860, eps: "−1", expr: "1971980·2^n−861", factor: "19", seconds: "0.28" },
  { k: 862, eps: "+1", expr: "1976566·2^n−861", factor: "1973", seconds: "0.32" },
  { k: 866, eps: "−1", expr: "1985738·2^n−867", factor: "673", seconds: "0.29" },
  { k: 868, eps: "+1", expr: "1990324·2^n−867", factor: "5", seconds: "0.27" },
  { k: 872, eps: "−1", expr: "1999496·2^n−873", factor: "5", seconds: "0.28" },
  { k: 874, eps: "+1", expr: "2004082·2^n−873", factor: "7", seconds: "0.28" },
  { k: 878, eps: "−1", expr: "2013254·2^n−879", factor: "31", seconds: "0.28" },
  { k: 880, eps: "+1", expr: "2017840·2^n−879", factor: "359", seconds: "0.33" },
  { k: 884, eps: "−1", expr: "2027012·2^n−885", factor: "761", seconds: "0.36" },
  { k: 886, eps: "+1", expr: "2031598·2^n−885", factor: "11", seconds: "0.27" },
  { k: 890, eps: "−1", expr: "2040770·2^n−891", factor: "7", seconds: "0.27" },
  { k: 892, eps: "+1", expr: "2045356·2^n−891", factor: "13", seconds: "0.27" },
  { k: 896, eps: "−1", expr: "2054528·2^n−897", factor: "11", seconds: "0.28" },
  { k: 898, eps: "+1", expr: "2059114·2^n−897", factor: "(none stored)", seconds: "0.28" },
  { k: 902, eps: "−1", expr: "2068286·2^n−903", factor: "(none stored)", seconds: "0.28" },
  { k: 904, eps: "+1", expr: "2072872·2^n−903", factor: "37993", seconds: "0.81" },
  { k: 908, eps: "−1", expr: "2082044·2^n−909", factor: "1156963663", seconds: "2.19 h" },
  { k: 910, eps: "+1", expr: "2086630·2^n−909", factor: "17", seconds: "0.27" },
  { k: 914, eps: "−1", expr: "2095802·2^n−915", factor: "167", seconds: "0.28" },
  { k: 916, eps: "+1", expr: "2100388·2^n−915", factor: "(none stored)", seconds: "0.28" },
  { k: 920, eps: "−1", expr: "2109560·2^n−921", factor: "50047", seconds: "0.95" },
  { k: 922, eps: "+1", expr: "2114146·2^n−921", factor: "73", seconds: "0.27" },
  { k: 926, eps: "−1", expr: "2123318·2^n−927", factor: "17", seconds: "0.27" },
  { k: 928, eps: "+1", expr: "2127904·2^n−927", factor: "5", seconds: "0.27" },
  { k: 932, eps: "−1", expr: "2137076·2^n−933", factor: "5", seconds: "0.27" },
  { k: 934, eps: "+1", expr: "2141662·2^n−933", factor: "29", seconds: "0.31" },
];

export function Rank100Page() {
  return (
    <main className="page notes lab-note-page">
      <h1>Rank 100 floor</h1>
      <p className="lede">
        PrimePages rank 100 is the Riesel q = 2293·2<sup>12918431</sup>−1
        (3,888,839 digits). Thin sieve at B = 10<sup>7</sup> left K
        <sub>cert</sub> = 98: first un-killed admissible multiplier. PFGW has since killed every admissible k through 934. No owner. k = 938 is in PFGW now.
      </p>
      <p>
        PFGW 4.1.8 on has-ams3-01, Intel Xeon Platinum 8280 @ 2.70 GHz, 8
        cores, 16 GB. n = 12,918,431. Admissible k are even and not divisible
        by 3. Skip multiples of 3. Snapshot 4 Oct 2026.
      </p>
      <div className="door-table-wrap">
        <table className="door-table">
          <thead>
            <tr>
              <th>k</th>
              <th>ε</th>
              <th>N</th>
              <th>factor</th>
              <th>time</th>
            </tr>
          </thead>
          <tbody>
            {FLOORS.map((row) => (
              <tr key={row.k}>
                <td>{row.k}</td>
                <td>{row.eps}</td>
                <td>
                  <code>{row.expr}</code>
                </td>
                <td>{row.factor}</td>
                <td>{row.seconds}</td>
              </tr>
            ))}
          </tbody>
        </table>
      </div>
      <p>
        k = 98 took 21 minutes to a nine-digit factor larger than B, so the
        thin sieve never saw it. k = 100 took 48 minutes (factor 393061223).
        Several later k die in a fraction of a second on a tiny prime. k = 104
        returned composite in 0.28 s with no factor stored in the walker JSON.
        k = 124 was the first to survive trial factoring to 1.66×10
        <sup>9</sup>. A full Fermat PRP then ran 25.7 h (81,312 s PRP + 11,162
        s other) and returned composite, RES64 C639D96377D4F918. The walker
        first logged that as unknown: it did not parse <code>is composite</code>.
        k = 128–140 died in 0.28 s on tiny primes the thin sieve never saw,
        because it stopped at the first survivor (k = 98). k = 142 was the
        second Fermat exam: 24.96 h (78,715 s PRP + 11,137 s other), composite,
        RES64 AC5D60C90B54F88D. Then 146–184 were 0.28 s jokes again. k = 148
        and 152 returned composite with no factor stored. k = 188 was the
        third Fermat exam: 25.02 h (79,056 s PRP + 11,024 s other), composite,
        RES64 85DDFCE797224332. Then 190–202 were 0.28 s again. k = 206 was the
        fourth Fermat exam: 24.34 h (76,647 s PRP + 10,986 s other), composite,
        RES64 A911EA4A4320C250. Then 208 and 212 died on 5. k = 214 was the
        fifth Fermat exam: 24.66 h (77,766 s PRP + 11,002 s other), composite,
        RES64 58D5F4C09BC76650. Then 218–226 were cheap kills (7, 18481, 641,
        11). k = 230 was a discount miss: factor 127891349 in 16 min (above
        B=10<sup>8</sup>, so not a Fermat). Then 232–322 were cheap kills
        again (296 took 124 s, factor 14146369). k = 326 was the sixth Fermat
        exam: 24.85 h, composite. Then 328–934 were killed as well: mostly cheap factors, with further Fermat composites at k = 442, 472, 626, 704, and 716, plus a 2.19 h factor at k = 908. k = 938 is in PFGW now — next survivor past the trial-factor bound. Eleven Fermat exams, eleven composites. Density, not the test. A
        40-hour gmpy2 Fermat on the Studio was the k = 98 check without the
        trial-factor gate.
      </p>
      <p>
        No owner yet. Walker: <code>analysis/rank100_pfgw_floors.py</code>
        (Xeon, k = 938 in PFGW — do not mix). Discount sieve:{" "}
        <code>analysis/rank100_discount.py</code> — special-form trial factor
        of every admissible k without building N, so 0.28 s jokes die before
        FFT. Survivors at B are the Fermat queue. Timing:{" "}
        <code>analysis/lab-metrics.json</code>.
      </p>
      <p className="home-actions">
        <Link className="nav-link" to="/certificates">
          Certificates
        </Link>
        <Link className="nav-link" to="/zeta-doors">
          Zeta doors
        </Link>
      </p>
    </main>
  );
}
