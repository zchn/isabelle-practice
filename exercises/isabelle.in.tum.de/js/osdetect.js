/* OS detection via JavaScript heuristics */

(function() {

function detect_os() {
  function p(n) { return navigator.platform.indexOf(n) != -1; }
  function a(n) { return navigator.userAgent.indexOf(n) != -1; }

  if (p("Linux") || a("Linux") || a("X11"))
    return "linux";
  else if (p("Mac") || a("Mac OS X") || a("MSIE 5.2"))
    return "darwin";
  else if (p("Win") || a("Win"))
    return "windows64";
  else
    return "linux darwin windows32 windows64";
}

function filterElements(e, f) {
  var c = e.firstChild;
  while(c != null) {
    var n = c.nextSibling;
    if (c.nodeType == document.ELEMENT_NODE) {
      if (! f(c)) {
        e.removeChild(c);
      }
    }
    c = n;
  }
}

function update_os_select() {
  var os = detect_os();
  document.body.className += os;

  var select = document.getElementById("os-select");
  var suggest = select.cloneNode(true);
  suggest.id = "os-suggest";
  select.parentNode.insertBefore(suggest, select);
  filterElements(suggest, function (e) { return os.indexOf(e.className) != -1; });
}

if(window.attachEvent) {
    window.attachEvent('onload', update_os_select);
} else {
    if(window.onload) {
        var curronload = window.onload;
        var newonload = function() {
            curronload();
            update_os_select();
        };
        window.onload = newonload;
    } else {
        window.onload = update_os_select;
    }
}

}) ()

