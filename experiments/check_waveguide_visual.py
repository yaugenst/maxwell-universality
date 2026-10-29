#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["playwright>=1.55,<2"]
# ///
"""Check the real interactive waveguide render and its archived numeric readouts."""
import json
from pathlib import Path
from playwright.sync_api import sync_playwright

OUT = Path(__file__).resolve().parent / "report/local_compilation/walkthrough"


def main():
    errors, checks = [], []
    data = json.loads((OUT / "waveguide_data.json").read_text())
    with sync_playwright() as p:
        browser = p.chromium.launch(executable_path="/usr/bin/google-chrome", headless=True)
        page = browser.new_page(viewport={"width": 780, "height": 1000}, device_scale_factor=1)
        page.on("pageerror", lambda e: errors.append(str(e)))
        page.goto((OUT / "preview.html").as_uri())
        frame = page.frame_locator("iframe")
        canvas = frame.locator("#wg-canvas")
        canvas.wait_for()
        frame.locator('#wg-values .wg-value').first.wait_for()
        for name, case in data["cases"].items():
            frame.locator('button[data-stage="1"]').click()
            frame.locator('#wg-case').select_option(name)
            for stage in range(5):
                frame.locator(f'button[data-stage="{stage}"]').click()
                assert canvas.get_attribute("data-stage") == str(stage)
                if stage == 0:
                    continue
                if stage >= 2:
                    count = len(case["ports"])
                    for choice in range(count+1):
                        frame.locator('#wg-input').select_option(str(choice))
                        b = ([float(i==choice) for i in range(count)] if choice<count else [1,-.6,.8,-.4][:count])
                        expected = [sum(v*w for v,w in zip(row,b)) for row in case["response"]]
                        actual = json.loads(canvas.get_attribute("data-response"))
                        assert max(abs(x-y) for x,y in zip(actual,expected)) < 1e-12
                        checks.append({"target":name,"stage":stage,"input":choice,"response":actual})
        frame.locator('button[data-stage="1"]').click()
        frame.locator('#wg-case').select_option("chain4")
        for width in (736, 360, 320):
            page.set_viewport_size({"width":width,"height":1200})
            page.wait_for_timeout(80)
            for stage in (0,1,3,4):
                frame.locator(f'button[data-stage="{stage}"]').click()
                if stage>=2:
                    frame.locator('#wg-input').select_option("4")
                overflow = frame.locator('#waveguide-local-compiler').evaluate("el => el.scrollWidth > el.clientWidth+1")
                assert not overflow, (width, stage)
                if width==736 or stage in (1,4):
                    frame.locator('#waveguide-local-compiler').screenshot(path=str(OUT/f"qa-{width}-stage{stage}.png"))
        page.set_viewport_size({"width":736,"height":1000})
        frame.locator('button[data-stage="1"]').click()
        frame.locator('#wg-case').select_option("mediator2")
        frame.locator('button[data-stage="3"]').click()
        frame.locator('#wg-input').select_option("0")
        frame.locator('#waveguide-local-compiler').screenshot(path=str(OUT/'qa-mediator.png'))
        frame.locator('#wg-view').select_option("section")
        frame.locator('#waveguide-local-compiler').screenshot(path=str(OUT/'qa-section.png'))
        page.emulate_media(color_scheme="dark")
        page.wait_for_timeout(80)
        frame.locator('#waveguide-local-compiler').screenshot(path=str(OUT/'qa-dark.png'))
        frame.locator('#waveguide-local-compiler').evaluate("""el => window.dispatchEvent(new CustomEvent('openai:set_globals', {
            detail: {globals: {widgetState: {modelContent: {target:'indefinite3',stage:4,input:3},privateContent:{view:'3d'}}}}
        }))""")
        assert canvas.get_attribute("data-target") == "indefinite3"
        assert canvas.get_attribute("data-stage") == "4"
        assert canvas.get_attribute("data-input") == "3"
        assert frame.locator('#wg-view').input_value() == '3d'
        assert not errors, errors
        browser.close()
    result = {"numeric_interactions":len(checks),"widths":[736,360,320],"dark_theme":True,
              "state_restore":True,"page_errors":errors,"checks":checks}
    (OUT/'browser_checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='checks'}))


if __name__ == '__main__':
    main()
