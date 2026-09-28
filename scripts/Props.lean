import X509.Widget

/-- Writes `X509.Widget.widgetProps` to `docs/props.json` for the browser version. -/
def main : IO Unit :=
  IO.FS.writeFile "docs/props.json" X509.Widget.widgetProps.compress
