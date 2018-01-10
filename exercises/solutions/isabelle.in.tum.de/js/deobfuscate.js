function dehex(s, i) { return "0123456789abcdef".indexOf(s.charAt(i)); }

function dehex_string(s) {
    var res = "";
    for(var i = 0; i < s.length; i += 2)
        res = res + String.fromCharCode(dehex(s, i) * 16 + dehex(s, i + 1));
    return res; }
    
function deobfuscate_email() {
    var elems = document.getElementsByTagName("a");
    for(var i = 0; i < elems.length; i++) {
        var a = elems[i];
        if (a.className == "obfuscate") {
            var email_hex = a.href.slice(8);
            var email = dehex_string(email_hex);
            a.href = "mailto:" + email;
            a.firstChild.nodeValue = email.split("?")[0]; } } }
            
function ie_readyState(func) {
    if(document.readyState == "interactive" || document.readyState == "complete")
        func(); }

if (document.addEventListener)
    document.addEventListener("DOMContentLoaded", deobfuscate_email, false);
else
    document.onreadystatechange = function() { ie_readyState(deobfuscate_email) }

