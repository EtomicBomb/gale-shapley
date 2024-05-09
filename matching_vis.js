//constants
const matching_grid_width = 100;
const stage_width = 530;
const stage_height = 723;

const initial_x_pos = 20;
const matching_grid_y_pos = 100;
const matching_grid_num_cols = 2;
const matching_grid_space = 30;
//initializing the stage
const stage = new Stage();
function initializeGrid(
  number_of_rows,
  num_of_cols,
  grid_x_location,
  grid_y_location
) {
  return new Grid({
    grid_location: { x: grid_x_location, y: grid_y_location },
    cell_size: {
      x_size: matching_grid_width / 2,
      y_size: matching_grid_width / 2,
    },
    grid_dimensions: {
      x_size: num_of_cols,
      y_size: number_of_rows,
    },
  });
}

function processMatches() {
  const matches = instance.signature("Matching").atoms();
  const matchingField = instance.field("matching");
  const matchingStateToMatches = {};

  matches.forEach((element, index) => {
    try {
      // Convert to a string for manipulation
      let px_rx_match = String(element.join(matchingField));
      // Split by whitespace or newline characters
      const items = px_rx_match.split(/[\s,\n]+/);
      console.log(`element: ${element} matches: ${px_rx_match}`);

      // a dictionary to store matching pairs
      const pxTorxDict = {};

      // Iterate through pairs of items (key-value) and store them
      for (let i = 0; i < items.length - 1; i += 2) {
        const key = items[i];
        const value = items[i + 1];
        pxTorxDict[key] = value;
        console.log(`items receiver ${value}`);
      }

      // maps matchingx to the inner dictionary pxTorxDict, which contains the matchings for each state
      console.log(`items ${items}`);
      matchingStateToMatches[String(element)] = pxTorxDict;
    } catch (error) {
      console.error(`Error processing Matching at index ${index}:`, error);
    }
  });

  console.log(
    `matchingStateToMatches: ${JSON.stringify(matchingStateToMatches)}`
  );
  return matchingStateToMatches;
}

function visualElementsForMatching() {
  const matches = processMatches();

  Object.entries(matches).forEach(([key, value], index) => {
    console.log(`key ${key}`);
    const num_of_rows = Object.entries(value).length;
    const grid_x_location =
      initial_x_pos + index * matching_grid_width + index * matching_grid_space;
    console.log(`rows ${num_of_rows}`);
    const grid = initializeGrid(
      num_of_rows,
      matching_grid_num_cols,
      grid_x_location,
      matching_grid_y_pos
    );
    let cleanedKey = key.replace(/[\[\]]/g, "");
    let matching_text = new TextBox({
      text: cleanedKey,
      coords: {
        x: grid_x_location + 50,
        y: matching_grid_y_pos - matching_grid_space,
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
        height: 30,
        width: 30,
        color: "blue",
        borderColor: "black",
        borderWidth: 1,
        label: px,
      });

      const receiverRect = new Rectangle({
        height: 30,
        width: 30,
        color: "red",
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
visualElementsForMatching();

stage.render(svg);
