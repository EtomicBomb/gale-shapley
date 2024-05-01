function initializeGrid(groupName, locationY, numRankings) {
  const groupElements = instance.signature(groupName).atoms();
  const numberOfElements = groupElements.length;
  return new Grid({
    grid_location: { x: 100, y: locationY },
    cell_size: { x_size: 40, y_size: 40 },
    grid_dimensions: {
      x_size: numRankings + 1, // number of people they're ranking plus 1
      y_size: numberOfElements + 1, // number of elements in the group plus 1
    },
  });
}
//helper function that returns each person's rankings in a sorted order
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
// Function to create visual elements and place them in grid cells
function createVisualElements(key, value, x, y, grid) {
  let keyString = key.toString();
  let firstLetter = keyString[0];
  let num_key = keyString.match(/\d+/) ? keyString.match(/\d+/)[0] : null;

  const rect = new Rectangle({
    height: 40,
    width: 40,
    color: "grey",
    borderColor: "black",
    borderWidth: 2,
    label: firstLetter + num_key,
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
      height: 40,
      width: 40,
      color: "grey",
      borderColor: "black",
      borderWidth: 2,
      label: index + 1,
    });
    grid.add({ x: x + 1 + index, y: y + 1 }, proposerBox);
    grid.add({ x: x + index + 1, y: 0 }, choices);
  });
}

function processRankings(group, fieldName, locationY) {
  const groupElements = instance.signature(group).atoms();
  const rankField = instance.field(fieldName);
  let numRankings = 0;
  let y = 0;
  let rankings = [];

  groupElements.forEach((element, index) => {
    try {
      let rankingsString = `${element.join(rankField)}`;
      let sortedPreferences = parseAndSortRankings(rankingsString);
      numRankings = Math.max(
        numRankings,
        Object.keys(sortedPreferences).length
      );
      rankings.push({ element, sortedPreferences, y });
      y++;
    } catch (error) {
      console.error(`Error processing ${group} at index ${index}:`, error);
    }
  });

  const grid = initializeGrid(group, locationY, numRankings);

  rankings.forEach(({ element, sortedPreferences, y }) => {
    createVisualElements(element, sortedPreferences, 0, y, grid);
  });

  return grid;
}

const receiverGrid = processRankings("Receiver", "rx_pref", 450);
const proposerGrid = processRankings("Proposer", "px_pref", 80);

const labels = [
  { text: "Receiver's Rankings", x: 220, y: 400, fontSize: 30 },
  { text: "Proposer's Rankings", x: 220, y: 30, fontSize: 30 },
  { text: "Proposers", x: 50, y: 200, fontSize: 12 },
  { text: "Receivers", x: 50, y: 570, fontSize: 12 },
  { text: "Ranks", x: 200, y: 60, fontSize: 12 },
  { text: "Ranks", x: 200, y: 430, fontSize: 12 },
];

const stage = new Stage();
labels.forEach((label) => {
  const textBox = new TextBox({
    text: label.text,
    coords: { x: label.x, y: label.y },
    color: "black",
    fontSize: label.fontSize,
  });
  stage.add(textBox);
});

stage.add(receiverGrid);
stage.add(proposerGrid);

stage.render(svg);
