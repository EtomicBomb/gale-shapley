// Grid and stage configuration constants
const gridWidth = 80;
const initialXPos = 50;
const initialYPos = 50;
const proposerGridYPos = 150;
const proposerGridNumCols = 3;
const proposerGridSpace = 30;
const grid_space = 200;
const receiverFields = instance.field("m_rx_prefs");
const proposerFields = instance.field("m_px_prefs");
const rxPrefSigField = instance.field("m_rx_pref");
const proposerPrefSigField = instance.field("m_px_pref");

const offer_grid_width = 100;
const stage_width = 530;
const stage_height = 723;
const offer_grid_y_pos = initialYPos + 2 * grid_space;
const offer_grid_num_cols = 2;

// Initialize the stage
const stage = new Stage();

// Function to initialize a grid with specified dimensions and location
function initializeGrid(
  numberOfRows,
  numOfCols,
  gridXLocation,
  gridYLocation,
  cellSize
) {
  return new Grid({
    grid_location: { x: gridXLocation, y: gridYLocation },
    cell_size: {
      x_size: cellSize / 2,
      y_size: cellSize / 2,
    },
    grid_dimensions: {
      x_size: numOfCols,
      y_size: numberOfRows,
    },
  });
}

// Function to parse and sort rankings
function parseAndSortRankings(rankingsString) {
  const preferencesArray = rankingsString.split(/[\s,\n]+/);
  let preferences = {};
  for (let i = 0; i < preferencesArray.length; i += 2) {
    let proposer = preferencesArray[i];
    let rank = parseInt(preferencesArray[i + 1], 10);
    if (!isNaN(rank)) {
      preferences[proposer] = rank;
    }
  }
  return Object.keys(preferences)
    .sort((a, b) => preferences[a] - preferences[b])
    .reduce((obj, key) => {
      obj[key] = preferences[key];
      return obj;
    }, {});
}

// Function to create and position visual elements in the grid
function createVisualElements(key, value, x, y, grid) {
  let keyString = key.toString();
  let firstLetter = keyString[0];
  let numKey = keyString.match(/\d+/) ? keyString.match(/\d+/)[0] : null;

  const rect = new Rectangle({
    height: gridWidth / 2 - 10,
    width: gridWidth / 2 - 10,
    color: "lightgrey",
    borderColor: "black",
    borderWidth: 2,
    label: firstLetter + numKey,
  });

  grid.add({ x: 0, y: y + 1 }, rect);

  Object.keys(value).forEach((proposer, index) => {
    let firstLetter1 = proposer[0];
    let match = proposer.match(/\d+/);
    let proposerLabel = firstLetter1 + match;
    const proposerBox = new TextBox({
      text: proposerLabel,
      color: "black",
      fontSize: 12,
    });
    const choices = new Rectangle({
      height: gridWidth / 2 - 10,
      width: gridWidth / 2 - 10,
      color: "lightgrey",
      borderColor: "black",
      borderWidth: 2,
      label: index + 1,
    });
    grid.add({ x: x + 1 + index, y: y + 1 }, proposerBox);
    grid.add({ x: x + index + 1, y: 0 }, choices);
  });
}

// Function to process elements and populate preferences for a given grid type
function processElementsAndPopulatePreferences(
  group,
  fields,
  sigField,
  gridXLocation,
  gridYLocation,
  gridSpace
) {
  const status = instance.signature(group).atoms();
  for (let i = 0; i < status.length; i++) {
    const elementsTuple = status[i].join(fields).tuples();
    for (let idx = 0; idx < elementsTuple.length; idx++) {
      const atms = elementsTuple[idx]._atoms;
      const receiverOrProposer = atms[0];
      const preferencesSignature = atms[1];
      const rankingString = `${preferencesSignature.join(sigField)}`;
      const keys = receiverOrProposer;
      console.log(`keys ${keys}`);

      const values = parseAndSortRankings(rankingString);
      const num_cols = Object.keys(values).length + 1;

      const grid = initializeGrid(
        elementsTuple.length + 1,
        num_cols,
        gridXLocation + gridSpace * i,
        gridYLocation,
        gridWidth
      );
      createVisualElements(keys, values, 0, idx, grid);
      stage.add(grid);

      let statusText = new TextBox({
        text: status[i],
        coords: {
          x: gridXLocation + gridSpace * i,
          y: gridYLocation - 20,
        },
        color: "black",
        fontSize: 14,
      });
      stage.add(statusText);
    }
  }
}

// Process and visualize the preferences
processElementsAndPopulatePreferences(
  "PxPrefs",
  proposerFields,
  proposerPrefSigField,
  initialXPos,
  initialYPos,
  grid_space
);
processElementsAndPopulatePreferences(
  "RxPrefs",
  receiverFields,
  rxPrefSigField,
  initialXPos,
  initialYPos + grid_space,
  grid_space
);
function processOffers() {
  const status = instance.signature("Status").atoms();
  const offerField = instance.field("offer");
  const stateToOffers = {};

  status.forEach((element, index) => {
    try {
      // Convert to a string for manipulation
      let px_rx_match = String(element.join(offerField));
      // Split by whitespace or newline characters
      const items = px_rx_match.split(/[\s,\n]+/);
      console.log(`element: ${element} offers: ${px_rx_match}`);

      // a dictionary to store matching pairs
      const pxTorxDict = {};

      // Iterate through pairs of items (key-value) and store them
      for (let i = 0; i < items.length - 1; i += 2) {
        const key = items[i];
        const value = items[i + 1];
        pxTorxDict[key] = value;
        console.log(`items receiver ${value}`);
      }

      // maps status to the inner dictionary pxTorxDict, which contains the offers
      console.log(`items ${items}`);
      stateToOffers[String(element)] = pxTorxDict;
    } catch (error) {
      console.error(`Error processing Matching at index ${index}:`, error);
    }
  });

  console.log(`stateToOffers: ${JSON.stringify(stateToOffers)}`);
  return stateToOffers;
}

function visualElementsForOffers() {
  const offers = processOffers();

  Object.entries(offers).forEach(([key, value], index) => {
    console.log(`key ${key}`);
    const num_of_rows = Object.entries(value).length;
    const grid_x_location = initialXPos + grid_space * index;
    console.log(`rows ${num_of_rows}`);
    const grid = initializeGrid(
      num_of_rows,
      offer_grid_num_cols,
      grid_x_location,
      offer_grid_y_pos,
      offer_grid_width
    );
    let cleanedKey = key.replace(/[\[\]]/g, "");
    let matching_text = new TextBox({
      text: cleanedKey,
      coords: {
        x: grid_x_location + (grid_space / 20) * index,
        y: offer_grid_y_pos - 20,
      },
      color: "black",
      fontSize: 14,
    });
    stage.add(matching_text);
    Object.entries(value).forEach(([key1, value1], index) => {
      const proposerMatch = key1.match(/\d+/);
      const receiverMatch = value1.match(/\d+/);
      const px = key1[0] + proposerMatch;
      const rx = value1[0] + receiverMatch;
      console.log(`${px} and ${rx}`);

      const proposerRect = new Rectangle({
        height: offer_grid_width / 2 - 10,
        width: offer_grid_width / 2 - 10,
        color: "#FDDE55",
        borderColor: "black",
        borderWidth: 1,
        label: px,
      });

      const receiverRect = new Rectangle({
        height: offer_grid_width / 2 - 10,
        width: offer_grid_width / 2 - 10,
        color: "#FF8888",
        borderColor: "black",
        borderWidth: 1,
        label: rx,
      });

      grid.add({ x: 0, y: index }, proposerRect);
      grid.add({ x: 1, y: index }, receiverRect);

      stage.add(grid);
    });
  });
}
visualElementsForOffers();

// Final rendering of the stage
stage.render(svg);
