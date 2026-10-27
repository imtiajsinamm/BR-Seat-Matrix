# BR Seat Matrix

**Version 0.9.3** — a browser userscript for the [Bangladesh Railway e-ticket website](https://eticket.railway.gov.bd/).

Search trains, inspect seat availability and calculated fares across station pairs, and plan split tickets.

## Features

- Search by route or load a train's route by train number.
- **Buy tickets ↗** on any By-route result jumps straight to the site's booking page for that train, with the fullest class preselected — no re-searching on the site.
- Scan station pairs for seat counts and fares by class.
- Refresh availability with **Rescan live**, or recall the last saved scan.
- Handle overnight routes with station-specific date offsets.
- Build a split-ticket plan, optionally prioritizing legs with fewer available seats.
- Open the booking flow for the next planned ticket. The helper attempts to select the matching train/class and the coach with the most seats; you still select seats and complete payment yourself.
- Use caching, request pacing, and retry backoff for rate-limited responses.

## Install

1. Install a browser userscript manager, such as Tampermonkey or Violentmonkey.
2. Open `BR Seat Matrix 0.9.3.user.js` from this repository and view its **Raw** contents. If your manager offers to install it, confirm the installation.
3. Alternatively, create a new script in your userscript manager, replace the editor contents with the entire file, and save it.
4. Visit `https://eticket.railway.gov.bd/`, log in normally, and reload the page.
5. Click the **Seat Matrix** button.

No build step or package installation is required for the script itself.

## Use

### By train

1. Choose the date the train leaves its **first station**.
2. Enter the train number and click **Load route**.
3. Choose the start and end stations, then click **Scan matrix**.
4. Use **Rescan live** when you need fresh availability.

### By route

1. Switch to **By route**.
2. Choose the date you leave your **From** station.
3. Enter the origin and destination, then click **Find trains**.
4. In the results, press **Buy tickets ↗** on a train to open its booking page on the site (the class with the most seats is preselected), or click a class chip to buy that specific class. Click the card body instead to load the train's full route into **By train** mode.

The Buy button opens the site's own search page with the route, date, train and class already filled in; the helper then clicks that train's **BOOK NOW** and switches to the coach with the most seats. You still choose seats and complete payment on the site.

### Split-ticket planning

Click a class entry in the matrix to add or remove a planned ticket. Use **Buy next** to open that leg's booking flow in another tab, then return to the plan and mark the ticket as bought after completing the purchase.

Separate legs are separate bookings. Availability can change between purchases; the plan does not reserve seats or guarantee a complete journey.

## Authentication and local data

- The script runs on `https://eticket.railway.gov.bd/*` with `@grant none`.
- It reads session authentication values from the site's browser storage and includes them in requests to `https://railspaapi.shohoz.com/v1.0/web`.
- It uses browser storage for cached results, the last scan, ticket plans, and panel preferences.
- Do not publish authentication tokens, device keys, cookies, or browser-storage exports. Review userscripts before installing them, especially on an authenticated site.

## Limitations

Website markup, API responses, availability, and fees can change. Displayed fares are calculated from API fare/VAT data and a configured berth fee; confirm the final price on the official booking page. Follow the website's terms and rate limits, and avoid unnecessary repeated scans.

The supplied JavaScript file is preserved byte-for-byte. A Node.js syntax check passed during packaging; live functionality and userscript-manager compatibility have not been tested as part of this packaging step.

To repeat the syntax-only check locally, with Node.js installed:

```sh
node --check "BR Seat Matrix 0.9.3.user.js"
```

## License

No license was supplied with the original script, and none has been added. The rights holder should choose a license before offering the code for reuse.
