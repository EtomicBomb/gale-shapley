// Grid and stage configuration constants
const gridWidth = 80;
const stageWidth = 1000;
const stageHeight = 1000;
const initialXPos = 50;
const initialYPos = 50;
const proposerGridYPos = 150;
const proposerGridNumCols = 3;
const proposerGridSpace = 30;
const receiverFields = instance.field("m_rx_prefs");
const proposerFields = instance.field("m_px_prefs");
const rxPrefSigField = instance.field("m_rx_pref");
const proposerPrefSigField = instance.field("m_px_pref");
let preferencesObject = {};

// Initialize the stage
const stage = new Stage({
  width: stageWidth,
  height: stageHeight,
});

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
    color: "grey",
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
      color: "grey",
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
  200
);
processElementsAndPopulatePreferences(
  "RxPrefs",
  receiverFields,
  rxPrefSigField,
  initialXPos,
  initialYPos + 200,
  200
);

// Final rendering of the stage
stage.render(svg);
