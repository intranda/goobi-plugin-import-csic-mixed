/**
 * This file is part of CamImportPlugins/SotonImportPlugins.
 * 
 * Copyright (C) 2011 intranda GmbH
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * @author Andrey Kozhushkov
 */
package de.intranda.goobi.plugins;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.io.StringWriter;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import net.xeoh.plugins.base.annotations.PluginImplementation;

import org.apache.commons.io.IOUtils;
import org.apache.commons.io.output.ByteArrayOutputStream;
import org.apache.commons.lang.StringUtils;
import org.apache.log4j.Logger;
import org.goobi.production.Import.DocstructElement;
import org.goobi.production.Import.ImportObject;
import org.goobi.production.Import.Record;
import org.goobi.production.enums.ImportReturnValue;
import org.goobi.production.enums.ImportType;
import org.goobi.production.enums.PluginType;
import org.goobi.production.plugin.interfaces.IImportPlugin;
import org.goobi.production.plugin.interfaces.IPlugin;
import org.goobi.production.properties.ImportProperty;
import org.jdom.Content;
import org.jdom.Namespace;
import org.jdom.Document;
import org.jdom.Element;
import org.jdom.JDOMException;
import org.jdom.input.SAXBuilder;
import org.jdom.output.Format;
import org.jdom.output.XMLOutputter;
import org.jdom.transform.XSLTransformer;

import ugh.dl.DigitalDocument;
import ugh.dl.DocStruct;
import ugh.dl.Fileformat;
import ugh.dl.Metadata;
import ugh.dl.MetadataType;
import ugh.dl.Prefs;
import ugh.exceptions.DocStructHasNoTypeException;
import ugh.exceptions.MetadataTypeNotAllowedException;
import ugh.exceptions.PreferencesException;
import ugh.exceptions.ReadException;
import ugh.exceptions.TypeNotAllowedAsChildException;
import ugh.exceptions.TypeNotAllowedForParentException;
import ugh.exceptions.WriteException;
import ugh.fileformats.mets.MetsMods;
import de.intranda.goobi.plugins.utils.ModsUtils;
import de.intranda.utils.CommonUtils;
import de.sub.goobi.Beans.Prozess;
import de.sub.goobi.Import.ImportOpac;
import de.sub.goobi.Persistence.ProzessDAO;
import de.sub.goobi.config.ConfigMain;
import de.sub.goobi.helper.FileUtils;
import de.sub.goobi.helper.exceptions.DAOException;
import de.sub.goobi.helper.exceptions.SwapException;

@PluginImplementation
public class CSICMixedImport implements IImportPlugin, IPlugin {

	/** Logger for this class. */
	private static final Logger logger = Logger.getLogger(CSICMixedImport.class);

	private static final String NAME = "CSICMixedImport";
	private static final String VERSION = "1.0.20120717";
	private static final String XSLT_PATH = ConfigMain.getParameter("xsltFolder") + "MARC21slim2MODS3.xsl";
	// private static final String XSLT_PATH = "resources/" + "MARC21slim2MODS3.xsl";
	// private static final String MODS_MAPPING_FILE = "resources/" + "mods_map.xml";
	private static final String MODS_MAPPING_FILE = ConfigMain.getParameter("xsltFolder") + "mods_map.xml";
	private static final String TEMP_DIRECTORY = ConfigMain.getParameter("tempfolder");

	private final static boolean deleteOriginalImages = false;
	private final static boolean deleteTempFiles = false;
	private final static boolean logConversionLoss = true;
	private final static boolean copyImages = false;
	private final static boolean updateExistingRecords = true;
	private final static boolean overrideExistingData = false;

	// Namespaces
	private Namespace mets;
	private Namespace premis;
	private Namespace mix;
	private Namespace marc;
	private Namespace goobi;
	private Namespace mods;

	private Prefs prefs;
	private String data = "";
	private File importFile = null;
	private String importFolder = "/output";
	private Map<String, String> map = new HashMap<String, String>();
	private Map<String, String> anchorMap = new HashMap<String, String>();
	private String currentIdentifier;
	private String currentTitle;
	private String currentAuthor;
	private List<String> currentCollectionList;
	private String encoding = "utf-8";
	private boolean isSeriesVolume = false;

	/**
	 * Directory containing the image files (possibly in TIFF/JPEG subfolders)
	 */
	public File exportFolder = new File("/mnt/csic/METS_0009");
	public File sourceFolder = null;
	public File logFolder = new File("/opt/digiverso/logs/CSIC");

	// private File exportFolder = new File("example");

	public CSICMixedImport() {
		map.put("?monographic", "Monograph");
		// map.put("?continuing", "Periodical");
		map.put("?continuing", "PeriodicalVolume");
		// map.put("?multipart monograph", "MultiVolumeWork");
		map.put("?multipart monograph", "Volume");
		map.put("?single unit", "Monograph");
		// map.put("?integrating resource", "MultiVolumeWork");
		map.put("?integrating resource", "Volume");
		// map.put("?serial", "Periodical");
		map.put("?serial", "SerialVolume");
		map.put("?cartographic", "Map");
		map.put("?notated music", null);
		map.put("?sound recording-nonmusical", null);
		map.put("?sound recording-musical", null);
		map.put("?moving image", null);
		map.put("?three dimensional object", null);
		map.put("?software, multimedia", null);
		map.put("?mixed material", null);

		anchorMap.put("Monograph", "Series");
		anchorMap.put("Manuscript", "Series");
		anchorMap.put("SerialVolume", "Series");
		anchorMap.put("Volume", "MultiVolumeWork");
		anchorMap.put("PeriodicalVolume", "Periodical");
	}

	/**
	 * Generates FileFormat from current data
	 */
	@Override
	public Fileformat convertData() {
		Document jDoc = convertDocument();
		Fileformat ff = null;
		if (jDoc != null) {
			try {
				// Write jDom Document to file and read it back as MetsMods (any possible anchor file is already created by convertDocument()
				File jDocFile = new File(importFolder, getProcessTitle());
				CommonUtils.getFileFromDocument(jDocFile, jDoc);
				ff = new MetsMods(prefs);
				ff.read(jDocFile.getAbsolutePath());

				// delete old files
				File importDir = new File(importFolder);
				for (File file : importDir.listFiles(XmlFilter)) {
					if (file.getName().contains(getProcessTitle()))
						file.delete();
				}
			} catch (IOException e) {
				logger.error(e.toString(), e);
			} catch (PreferencesException e) {
				logger.error(e.toString(), e);
			} catch (ReadException e) {
				logger.error(e.toString(), e);
			}
		}

		return ff;
	}

	/**
	 * replaces convertData() - returns a jDOM document rather than a Fileformat
	 * 
	 * @return
	 */
	public Document convertDocument() {
		if (data == null || data.isEmpty()) {
			logger.warn("Attempting to convert empty data. Aborting.");
			return null;
		}

		Document modsDoc = null;
		Document marcDoc = null;
		Document doc = null;
		File tempFile = new File(TEMP_DIRECTORY, "temp_" + System.currentTimeMillis() + ".xml");
		logger.debug("Creating temporary file " + tempFile.getAbsolutePath());
		try {
			doc = CommonUtils.getDocumentFromString(data);
			getNamespaces(doc.getRootElement());
			marcDoc = getMarcDocument(doc);
			String marcString = getStringFromDocument(marcDoc, encoding);
			Fileformat ff = convertData(marcString);
			if (ff != null) {
				ff.write(tempFile.getAbsolutePath());

			} else {
				logger.error("Failed to convert marc doc");
				return null;
			}
			modsDoc = CommonUtils.getDocumentFromFile(tempFile);
			getNamespaces(modsDoc.getRootElement());

		} catch (WriteException e) {
			logger.error(e.toString(), e);
		} catch (PreferencesException e) {
			logger.error(e.toString(), e);
		}

		verifyIdentifier();
		doc = replaceXmlData(doc, modsDoc);
		doc = exchangeStructData(doc);
		doc = replaceStructData(doc, modsDoc);

		File anchorFile = new File(tempFile.getAbsolutePath().replace(".xml", "_anchor.xml"));
		if (deleteTempFiles && anchorFile.isFile()) {
			anchorFile.renameTo(new File(importFolder, getProcessTitle().replace(".xml", "_anchor.xml")));
		} else if (anchorFile.isFile()) {
			try {
				copyFile(anchorFile, new File(importFolder, getProcessTitle().replace(".xml", "_anchor.xml")));
				if (sourceFolder != null && sourceFolder.isDirectory()) {
					anchorFile.renameTo(new File(sourceFolder, anchorFile.getName()));
				}
			} catch (IOException e) {
				logger.error(e.getMessage(), e);
			}
		}
		if (deleteTempFiles && tempFile.exists()) {
			tempFile.delete();
		} else if (sourceFolder != null && sourceFolder.isDirectory()) {
			tempFile.renameTo(new File(sourceFolder, tempFile.getName()));
		}

		return doc;
	}

	private static DecimalFormat volumeNumberFormat = new DecimalFormat("00");
	private static ArrayList<String> identifiers = new ArrayList<String>();

	private void verifyIdentifier() {
		boolean exists = false;
		for (String id : identifiers) {
			if (currentIdentifier.contentEquals(id)) {
				exists = true;
			}
		}
		File existingData = searchForExistingData(currentIdentifier);
		if (existingData != null) {
			if (overrideExistingData) {
				// TODO
			} else {
				exists = true;
			}
		}

		if (exists) {
			// there is already a process of this name, either in Goobi, or in the list of imports
			String[] parts = currentIdentifier.split("_");
			if (parts != null && parts.length > 0) {
				String end = parts[parts.length - 1];
				if (end.startsWith("V") && end.length() == 3) {
					// identifier already has a volume suffix, create a new one
					int volume = 2;
					try {
						volume = Integer.valueOf(end.replaceAll("\\D", ""));
					} catch (NumberFormatException e) {
						logger.error("Found a volume suffix in the identifier, but couldn't resolve the volume number");
					}
					end = "V" + volumeNumberFormat.format(volume);
					parts[parts.length - 1] = end;
					// and rebuild identifier
					currentIdentifier = "";
					for (int i = 0; i < parts.length; i++) {
						currentIdentifier += parts[i];
					}
				} else {
					currentIdentifier += "_V02";
				}
			} else {
				currentIdentifier += "_V02";
			}
			// check again ifthis identifier already exists
			verifyIdentifier();
		} else {
			// unused identifier. User this and add to list
			identifiers.add(currentIdentifier);
		}
	}

	/**
	 * 
	 * generate mets files and copy image files from record list
	 * 
	 */
	@Override
	public List<ImportObject> generateFiles(List<Record> records) {
		ArrayList<ImportObject> ret = new ArrayList<ImportObject>();

		if (importFolder != null) {
			// sourceFolder =
		}

		for (Record r : records) {
			logger.info("Processing " + r.getId());
			// Data conversion
			data = r.getData();
			currentCollectionList = r.getCollections();
			Fileformat ff = convertData();

			ImportObject io = new ImportObject();

			if (ff != null) {
				// writing converted data into Import("temp") folder
				try {
					MetsMods mm = new MetsMods(prefs);
					mm.setDigitalDocument(ff.getDigitalDocument());
					String fileName = getImportFolder() + getProcessTitle();
					logger.debug("Writing '" + fileName + "'...");
					mm.write(fileName);
					logger.debug("copying image files...");
					copyImageFiles(exportFolder, r);
					io.setProcessTitle(getProcessTitle().replace(".xml", ""));
					io.setMetsFilename(fileName);
					io.setImportReturnValue(ImportReturnValue.ExportFinished);
					if (importFile != null && sourceFolder != null) {
						importFile.renameTo(new File(sourceFolder, importFile.getName()));
					}
				} catch (PreferencesException e) {
					logger.error(e.getMessage(), e);
					io.setImportReturnValue(ImportReturnValue.InvalidData);
					io.setErrorMessage(e.getMessage());
				} catch (WriteException e) {
					logger.error(e.getMessage(), e);
					io.setImportReturnValue(ImportReturnValue.WriteError);
					io.setErrorMessage(e.getMessage());
				}
			} else {
				io.setImportReturnValue(ImportReturnValue.InvalidData);
				io.setErrorMessage("FileFormat is null");
			}
			ret.add(io);
		}
		return ret;
	}

	/**
	 * generate list of records
	 * 
	 */
	@Override
	public List<Record> generateRecordsFromFile() {
		List<Record> ret = new ArrayList<Record>();

		if (importFile.getName().endsWith("zip")) {
			logger.info("Extracting zip archive");
			HashMap<String, byte[]> recordStrings = unzipFile(importFile);
			HashMap<String, String> filteredRecordStrings = new HashMap<String, String>();

			// Check all records first to see what's inside
			int count = 0;
			for (String key : recordStrings.keySet()) {
				byte[] bytes = recordStrings.get(key);
				InputStream bais = null;
				if (key.endsWith(".zip")) {
					// Another zip-archive
					logger.debug("Extracting inner archive " + key + "; size = " + bytes.length + " bytes");
					try {
						bais = new ByteArrayInputStream(bytes);
						// FileOutputStream fout = new FileOutputStream(new File(importFolder, "temp.zip"));
						// fout.write(bytes);
						// fout.close();
						HashMap<String, String> tempRecords = unzipStream(bais);
						filteredRecordStrings.putAll(tempRecords);
					} catch (Exception e) {
						logger.error("Unable to read inner zip file");
					} finally {
						if (bais != null) {
							try {
								bais.close();
							} catch (IOException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
						}
					}
				} else if (key.endsWith(".xml")) {
					filteredRecordStrings.put(key, bytes.toString());
				}
			}

			count = 0;
			for (String key : filteredRecordStrings.keySet()) {
				String importFileName = key;
				String importData = filteredRecordStrings.get(key);
				logger.debug("Extracting record " + ++count);
				Record rec = new Record();
				rec.setData(importData);
				rec.setId(importFileName.substring(0, importFileName.indexOf(".")));
				// check for old records
				File oldFile = searchForExistingData(/* "CSIC" + */rec.getId());
				if (updateExistingRecords && oldFile != null) {
					logger.info("Found existing record. Updating.");
					updateOldRecord(rec, oldFile);
				} else {
					ret.add(rec);
				}
			}
		} else {
			logger.info("Importing single record file");
			InputStream input = null;
			StringWriter writer = null;
			try {
				logger.debug("loaded file: " + importFile.getAbsolutePath());
				input = new FileInputStream(importFile);
				Record record = new Record();
				writer = new StringWriter();
				IOUtils.copy(input, writer, encoding);
				record.setData(writer.toString());
				record.setId(importFile.getName().split("_")[0]);
				// check for old records
				File oldFile = searchForExistingData("CSIC" + record.getId());
				if (oldFile != null) {
					logger.info("Found existing record. Updating.");
					updateOldRecord(record, oldFile);
				} else {
					ret.add(record);
				}
			} catch (FileNotFoundException e) {
				logger.error(e.getMessage(), e);
			} catch (IOException e) {
				logger.error(e.getMessage(), e);
			} finally {
				if (input != null) {
					try {
						if (writer != null)
							writer.close();
						input.close();
					} catch (IOException e) {
						logger.error(e.getMessage(), e);
					}
				}
				if (ret.size() > 0 && importFile != null)
					logger.info("Extracted " + ret.size() + " records from '" + importFile.getName() + "'.");
				else
					logger.error("No record extracted from importFile");
			}
		}

		return ret;
	}

	/**
	 * not used - records are split on import
	 */
	@Override
	public List<Record> splitRecords(String records) {

		return null;
	}

	@Override
	public List<String> splitIds(String ids) {
		return null;
	}

	@Override
	public String getProcessTitle() {
		if (StringUtils.isNotBlank(currentTitle)) {
			return new ImportOpac().createAtstsl(currentTitle, currentAuthor).toLowerCase() + "_" + currentIdentifier + ".xml";
		}
		return currentIdentifier + ".xml";
	}

	@Override
	public void setData(Record r) {
		this.data = r.getData();
	}

	@Override
	public String getImportFolder() {
		return importFolder;
	}

	@Override
	public void setImportFolder(String folder) {
		this.importFolder = folder;
	}

	@Override
	public void setFile(File importFile) {
		this.importFile = importFile;
	}

	@Override
	public void setPrefs(Prefs prefs) {
		this.prefs = prefs;

	}

	@Override
	public List<ImportType> getImportTypes() {
		List<ImportType> answer = new ArrayList<ImportType>();
		answer.add(ImportType.FILE);

		return answer;
	}

	@Override
	public PluginType getType() {
		return PluginType.Import;
	}

	@Override
	public String getTitle() {
		return getDescription();
	}

	@Override
	public String getId() {
		return getDescription();
	}

	@Override
	public String getDescription() {
		return NAME + " v" + VERSION;
	}

	/**
	 * 
	 * Specialized convertData to convert only the specified String inString from marc to mods
	 * 
	 * @param inString
	 * @return
	 */
	private Fileformat convertData(String inString) {
		Fileformat ff = null;
		Document doc;
		try {
			doc = new SAXBuilder().build(new StringReader(inString));

			// remove namespaces
			Element docRoot = doc.getRootElement();
			docRoot = setNamespaceRecursive(docRoot, null);
			Element newRecord = new Element("record");
			List<Element> eleList = new ArrayList<Element>();
			for (Object obj : docRoot.getChildren()) {
				Element child = (Element) obj;
				eleList.add(child);
			}
			for (Element element : eleList) {
				element.detach();
			}
			newRecord.setContent(eleList);
			for (Object obj : newRecord.getChildren()) {
				Element child = (Element) obj;
				child.setNamespace(null);
			}
			// newRecord = removeDuplicateChildren(newRecord);
			docRoot.detach();
			doc.setRootElement(newRecord);

			// logger.debug(new XMLOutputter().outputString(doc));
			if (doc != null && doc.hasRootElement()) {
				XSLTransformer transformer = new XSLTransformer(XSLT_PATH);
				Document docMods = transformer.transform(doc);

				// logger.debug(new XMLOutputter().outputString(docMods));
				ff = new MetsMods(prefs);
				DigitalDocument dd = new DigitalDocument();
				ff.setDigitalDocument(dd);

				Element eleMods = docMods.getRootElement();
				if (eleMods.getName().equals("modsCollection")) {
					eleMods = eleMods.getChild("mods", null);
				}

				// Determine the root docstruct type
				String dsType = "Monograph";
				String dsAnchorType = "Series";
				if (eleMods.getChild("originInfo", null) != null) {
					Element eleIssuance = eleMods.getChild("originInfo", null).getChild("issuance", null);
					if (eleIssuance != null && map.get("?" + eleIssuance.getTextTrim()) != null) {
						dsType = map.get("?" + eleIssuance.getTextTrim());
					}
				}
				Element eleTypeOfResource = eleMods.getChild("typeOfResource", null);
				if (eleTypeOfResource != null) {
					if ("yes".equals(eleTypeOfResource.getAttributeValue("manuscript"))) {
						// Manuscript
						dsType = "Manuscript";
					} else if (map.get("?" + eleTypeOfResource.getTextTrim()) != null) {
						dsType = map.get("?" + eleTypeOfResource.getTextTrim());
					}
				}

				dsAnchorType = anchorMap.get(dsType);
				// dsType = "Volume";
				logger.debug("Docstruct type: " + dsType);
				DocStruct dsRoot = dd.createDocStruct(prefs.getDocStrctTypeByName(dsAnchorType));
				if (dsRoot == null) {
					logger.error("Could not create DocStructType " + dsAnchorType);
				}
				DocStruct dsVolume = dd.createDocStruct(prefs.getDocStrctTypeByName(dsType));
				if (dsVolume == null) {
					logger.error("Could not create DocStructType " + dsVolume);
					return null;
				}

				DocStruct dsBoundBook = dd.createDocStruct(prefs.getDocStrctTypeByName("BoundBook"));
				dd.setPhysicalDocStruct(dsBoundBook);
				// Collect MODS metadata
				ModsUtils.parseModsSection(MODS_MAPPING_FILE, prefs, dsVolume, dsBoundBook, dsRoot, eleMods);
				currentIdentifier = ModsUtils.getIdentifier(prefs, dsVolume);
				currentTitle = ModsUtils.getTitle(prefs, dsVolume);
				currentAuthor = ModsUtils.getAuthor(prefs, dsVolume);
				logger.debug("Author:" + currentAuthor + ", Title: " + currentTitle);

				// create source ("import") Folder
				if (importFolder != null) {
					File tempDir = new File(importFolder, getProcessTitle().replace(".xml", ""));
					sourceFolder = new File(tempDir, "import");
					sourceFolder.mkdirs();
				}

				// Check if we are part of a series, and if so, create logical DocStruct accordingly
				try {
					List<? extends Metadata> seriesIDList = dsRoot.getAllMetadataByType(prefs.getMetadataTypeByName("CatalogIDDigital"));
					// for (Metadata metadata : seriesIDList) {
					// }
					if (seriesIDList != null && !seriesIDList.isEmpty()) {
						logger.debug("Record is part of a series");
						isSeriesVolume = true;
						dsRoot.addChild(dsVolume);
						dd.setLogicalDocStruct(dsRoot);
					} else {
						dd.setLogicalDocStruct(dsVolume);
						logger.debug("Record is not part of a series");
						isSeriesVolume = false;
					}
				} catch (TypeNotAllowedAsChildException e) {
					logger.error("Child Type not allowed", e);
				}

				if (logConversionLoss) {
					File marcLossFile = new File(logFolder, currentIdentifier + "_MarcLoss.xml");
					Document lossDoc = getMarcModsLoss(doc, docMods);
					CommonUtils.getFileFromDocument(marcLossFile, lossDoc);
					File modsFile = new File(logFolder, currentIdentifier + "_Mods.xml");
					try {
						CommonUtils.getFileFromDocument(modsFile, docMods);
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}

				if (!deleteTempFiles) {
					File modsFile = new File(sourceFolder, "modsTemp.xml");
					try {
						CommonUtils.getFileFromDocument(modsFile, docMods);
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}

				// Add 'pathimagefiles'
				try {
					Metadata mdForPath = new Metadata(prefs.getMetadataTypeByName("pathimagefiles"));
					mdForPath.setValue("./" + currentIdentifier);
					dsBoundBook.addMetadata(mdForPath);
				} catch (MetadataTypeNotAllowedException e1) {
					logger.error("MetadataTypeNotAllowedException while reading images", e1);
				} catch (DocStructHasNoTypeException e1) {
					logger.error("DocStructHasNoTypeException while reading images", e1);
				}

				// Add collection names attached to the current record
				if (currentCollectionList != null) {
					MetadataType mdTypeCollection = prefs.getMetadataTypeByName("singleDigCollection");
					for (String collection : currentCollectionList) {
						Metadata mdCollection = new Metadata(mdTypeCollection);
						mdCollection.setValue(collection);
						dsRoot.addMetadata(mdCollection);
					}
				}
			}

		} catch (JDOMException e) {
			logger.error(e.getMessage(), e);
			return null;
		} catch (IOException e) {
			logger.error(e.getMessage(), e);
		} catch (PreferencesException e) {
			logger.error(e.getMessage(), e);
		} catch (TypeNotAllowedForParentException e) {
			logger.error(e.getMessage(), e);
		} catch (MetadataTypeNotAllowedException e) {
			logger.error(e.getMessage(), e);
		}

		return ff;
	}

	/**
	 * returns the metadatafile meta.xml if a prozess of this name was found, null otherwise
	 * 
	 * @param processTitle
	 * @return
	 */
	private File searchForExistingData(String processTitle) {
		String metsFilePath, processDataDirectory;
		ProzessDAO dao = new ProzessDAO();

		try {
			List<Prozess> processList = dao.search("from Prozess where titel LIKE '%" + processTitle + "'");

			if (processList != null && !processList.isEmpty()) {
				Prozess p = processList.get(0);
				logger.info("Found existing process '" + p.getTitel() + "'...");
				metsFilePath = p.getMetadataFilePath();
				processDataDirectory = p.getProcessDataDirectory();
				logger.debug("METS file path: " + metsFilePath);
				logger.debug("Process data path: " + processDataDirectory);
				File metadataFile = new File(metsFilePath);
				return metadataFile;
			}
		} catch (DAOException e) {
			logger.error(e.toString());
		} catch (SwapException e) {
			logger.error(e.toString());
		} catch (IOException e) {
			logger.error(e.toString());
		} catch (InterruptedException e) {
			logger.error(e.toString());
		}
		return null;
	}

	/**
	 * returns the metadatafile meta.xml if a prozess of this name was found, null otherwise
	 * 
	 * @param processTitle
	 * @return
	 */
	public static File DeleteExistingData(String processTitle) {
		String processDataDirectory = null;
		ProzessDAO dao = new ProzessDAO();

		try {
			List<Prozess> processList = dao.search("from Prozess where titel LIKE '%" + processTitle + "%'");

			logger.debug("Deleting " + processList.size() + "data sets.");
			if (processList != null && !processList.isEmpty()) {
				for (Prozess prozess : processList) {
					processDataDirectory = prozess.getProcessDataDirectory();
					dao.remove(prozess);
				}
				File prozessDir = new File(processDataDirectory);
				deleteOldDirs(prozessDir.getParentFile(), processTitle);
			}
		} catch (DAOException e) {
			logger.error(e.toString(), e);
		} catch (SwapException e) {
			logger.error(e.toString(), e);
		} catch (IOException e) {
			logger.error(e.toString(), e);
		} catch (InterruptedException e) {
			logger.error(e.toString(), e);
		}
		return null;
	}

	/**
	 * Deletes all goobi metadata directories contianing prozesses oft the given identifier
	 * 
	 * @param parentDir
	 * @param identifier
	 */
	private static void deleteOldDirs(File parentDir, String identifier) {
		File[] dirs = parentDir.listFiles(DirFilter);
		boolean delete = false;

		for (File dir : dirs) {
			File imageDir = new File(dir, "images");
			if (imageDir.isDirectory()) {
				File[] imageDirChildren = imageDir.listFiles(DirFilter);
				for (File childDir : imageDirChildren) {
					if (childDir.getName().contains(identifier))
						delete = true;
					break;
				}
			} else
				delete = true;
			if (delete) {
				logger.info("Deleting directory " + dir.getName());
				CommonUtils.deleteDir(dir);
			}
		}

	}

	/**
	 * 
	 * creates a backup of the oldMetaFile and replaces the metafile with the Record record
	 * 
	 * @param record
	 * @param oldMetaFile
	 */
	private void updateOldRecord(Record record, File oldMetaFile) {

		data = record.getData();
		currentCollectionList = record.getCollections();
		Document newDoc = convertDocument();
		logger.info("Replacing old matadata in metadata folder " + oldMetaFile.getParent() + " with new data");

		// renaming old metadata files to keep as backup
		String newMetaFileName = oldMetaFile.getAbsolutePath();
		File oldAnchorFile = new File(oldMetaFile.getParent(), "meta_anchor.xml");
		if (oldAnchorFile.isFile()) {
			oldAnchorFile.renameTo(new File(oldMetaFile.getParent(), oldAnchorFile.getName().replace(".xml", ".preIntrandaImport.xml")));
		}
		oldMetaFile.renameTo(new File(oldMetaFile.getParent(), oldMetaFile.getName().replace(".xml", ".preIntrandaImport.xml")));
		try {
			if (newDoc == null) {
				logger.error("Mets document is null. Aborting import");
			}
			String fileName = newMetaFileName;
			logger.debug("Writing '" + fileName + "' into existing folder...");
			CommonUtils.getFileFromDocument(new File(fileName), newDoc);

			// getting anchor file
			File importDir = new File(importFolder);
			if (!importDir.isDirectory()) {
				logger.warn("no hotfolder found. Cannot get anchor files");
			} else {
				for (File file : importDir.listFiles(XmlFilter)) {
					if (file.getName().contains(record.getId() + "_anchor")) {
						logger.debug("Moving file " + file.getName() + " to metadata folder");
						file.renameTo(new File(oldMetaFile.getParent(), "meta_anchor.xml"));
						break;
					}
				}

				// updating import folders
				if (sourceFolder != null && sourceFolder.isDirectory()) {
					File tempDir = sourceFolder.getParentFile();
					File metadataDir = oldMetaFile.getParentFile();

					File[] files = tempDir.listFiles();
					if (files != null) {
						for (File file : files) {
							File newFile = new File(metadataDir, file.getName());
							if (file.isDirectory()) {
								int counter = 0;
								while (newFile.isDirectory()) {
									newFile = new File(newFile.getParent(), newFile.getName() + counter);
									counter++;
								}
								org.apache.commons.io.FileUtils.copyDirectory(file, newFile);
							} else if (file.isFile()) {
								int counter = 0;
								while (newFile.isFile()) {
									String fileNameTrunk = newFile.getName().substring(0, newFile.getName().indexOf("."));
									String fileNameExt = newFile.getName().substring(newFile.getName().indexOf("."));
									newFile = new File(newFile.getParent(), fileNameTrunk + counter + fileNameExt);
									counter++;
								}
								org.apache.commons.io.FileUtils.copyDirectory(file, newFile);
							}
						}
					}
				}

				// purging old temp files
				// for (File file : importDir.listFiles(XmlFilter)) {
				// if(file.getName().contains(record.getId()))
				// file.delete();
				// }
			}

			// ret.put(getProcessTitle(), ImportReturnValue.ExportFinished);
		} catch (IOException e) {
			logger.error(e.getMessage(), e);
		}

	}

	/**
	 * Removes all duplicate occurences of marc datafields with the same same tag
	 * 
	 * @param newRecord
	 * @return
	 */
	@SuppressWarnings({ "unchecked", "unused" })
	private Element removeDuplicateChildren(Element newRecord) {
		Element newnewRecord = new Element(newRecord.getName());
		List<Element> children = newRecord.getChildren();
		List<String> tags = new ArrayList<String>();
		logger.debug("Cecking for duplicate datafields in " + children.size() + " fields");
		for (Element child : children) {
			if (child.getAttribute("tag") != null && tags.contains(child.getAttributeValue("tag"))) {
				logger.debug("Found duplicate MARC field with tag " + child.getAttributeValue("tag"));
			} else {
				logger.debug("Added tag " + child.getAttributeValue("tag") + " to tag list");
				newnewRecord.addContent((Element) child.clone());
				tags.add(child.getAttributeValue("tag"));
			}
		}

		return newnewRecord;
	}

	/**
	 * Extract marc section from import document and return it as its own document
	 * 
	 * @param inDoc
	 * @return
	 */
	private Document getMarcDocument(Document inDoc) {
		Element marcRecord = null;

		// getting document elements
		Element root = inDoc.getRootElement();

		logger.debug("getting document elements");
		if (root != null) {
			if (root.getChildren().isEmpty())
				logger.warn("No children found in root");
			else {
				marcRecord = root.getChild("dmdSec", mets).getChild("mdWrap", mets).getChild("xmlData", mets).getChild("marc", marc)
						.getChild("record", marc);
			}
		} else
			logger.warn("Root element not found");
		marcRecord.detach();
		return new Document(marcRecord);
	}

	/**
	 * Get the namespaces using Element root
	 * 
	 * @param root
	 */
	private void getNamespaces(Element root) {
		mets = root.getNamespace("mets");
		if (mets != null)
			logger.debug("Namespace mets: Prefix = " + mets.getPrefix() + ", uri = " + mets.getURI());
		premis = root.getNamespace("premis");
		if (premis != null)
			logger.debug("Namespace premis: Prefix = " + premis.getPrefix() + ", uri = " + premis.getURI());
		mix = root.getNamespace("mix");
		if (mix != null)
			logger.debug("Namespace mix: Prefix = " + mix.getPrefix() + ", uri = " + mix.getURI());
		marc = root.getNamespace("marc");
		if (marc != null)
			logger.debug("Namespace marc: Prefix = " + marc.getPrefix() + ", uri = " + marc.getURI());
		goobi = root.getNamespace("goobi");
		if (goobi != null)
			logger.debug("Namespace goobi: Prefix = " + goobi.getPrefix() + ", uri = " + goobi.getURI());
		mods = root.getNamespace("mods");
		if (mods != null)
			logger.debug("Namespace mods: Prefix = " + mods.getPrefix() + ", uri = " + mods.getURI());
	}

	/**
	 * 
	 * Creates a single String out of the Document document
	 * 
	 * @param document
	 * @param encoding
	 * @return
	 */
	private String getStringFromDocument(Document document, String encoding) {
		if (document == null) {
			logger.warn("Trying to convert null document to String. Aborting");
			return null;
		}
		XMLOutputter outputter = new XMLOutputter();
		Format xmlFormat = outputter.getFormat();
		if (!(encoding == null) && !encoding.isEmpty())
			xmlFormat.setEncoding(encoding);
		xmlFormat.setExpandEmptyElements(true);
		outputter.setFormat(xmlFormat);
		String docString = outputter.outputString(document);

		return docString;
	}

	/**
	 * Gets the "TYPE" of the logical structmap in Document doc
	 * 
	 * @param doc
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private String getLogicalType(Document doc) {
		List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);
		String type = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL")) {
				type = element.getChild("div", mets).getAttributeValue("TYPE");
				logger.debug("Found logical root type in marc document: " + type);
			}
		}
		return type;
	}

	/**
	 * Gets the "TYPE" of the logical structmap in Document doc
	 * 
	 * @param doc
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private String getLogicalSubType(Document doc) {
		List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);
		String type = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL")) {

				Element series = element.getChild("div", mets);

				type = series.getChild("div", mets).getAttributeValue("TYPE");
				logger.debug("Found logical root type in marc document: " + type);
			}
		}
		return type;
	}

	/**
	 * Gets the "TYPE" of the physical structmap in Document doc
	 * 
	 * @param doc
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private String getPhysicalType(Document doc) {
		List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);
		String type = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL")) {
				type = element.getChild("div", mets).getAttributeValue("TYPE");
				logger.debug("Found physical root type in marc document: " + type);
			}
		}
		return type;
	}

	/**
	 * 
	 * Copy the files in exportFolder corresponding to the current record into the importFolder
	 * 
	 * @param exportFolder
	 */
	private void copyImageFiles(File exportFolder, Record r) {

		if (!copyImages) {
			return;
		}

		String id = currentIdentifier.replace("CSIC", "");

		if (!exportFolder.isDirectory()) {
			logger.warn("export folder does not exist. Cannot copy image files");
			return;
		}

		List<File> folders = Arrays.asList(exportFolder.listFiles());
		File tiffDir = null, jpegDir = null, parentImageDir = null;
		ArrayList<File> imageDirs = new ArrayList<File>();
		for (File file : folders) {
			if (file.isDirectory() && file.getName().toLowerCase().contentEquals("tiff")) {
				logger.debug("found \"tiff\" directory in " + exportFolder.getName());
				tiffDir = file;
			}
			if (file.isDirectory() && (file.getName().toLowerCase().contentEquals("jpg") || file.getName().toLowerCase().contentEquals("difusion"))) {
				logger.debug("found \"jpeg\" directory in " + exportFolder.getName());
				jpegDir = file;
			}
		}

		// set the appropriate parent directory containing the image archives
		if (tiffDir == null || !tiffDir.isDirectory()) {
			if (jpegDir == null || !jpegDir.isDirectory()) {
				parentImageDir = exportFolder;
			} else {
				parentImageDir = jpegDir;
			}
		} else {
			parentImageDir = tiffDir;
		}

		List<File> processFolders = Arrays.asList(parentImageDir.listFiles());
		for (File file : processFolders) {
			if (file.isDirectory() && file.getName().contains(r.getId())) {
				imageDirs.add(file);
				logger.debug("found export folder " + file.getName() + " in " + parentImageDir);
			}
		}

		// // with no tiff dir, we assume the process directories are directly
		// // within exportFolder
		// if (tiffDir == null) {
		// for (File folder : folders) {
		// if (folder.isDirectory() && folder.getName().contains(id)) {
		// imageDir = folder;
		// logger.debug("found export folder " + imageDir + " in " + exportFolder);
		// }
		// }
		// } else {
		// // search in tiff-dir
		// folders = Arrays.asList(tiffDir.listFiles());
		// for (File folder : folders) {
		// if (folder.isDirectory() && folder.getName().contains(id))
		// imageDir = folder;
		// }
		// // if tiff-dir is empty or non-existant, search again in jpg dir
		// if (imageDir == null || imageDir.listFiles() == null || imageDir.listFiles().length == 0) {
		// folders = Arrays.asList(jpegDir.listFiles());
		// for (File folder : folders) {
		// if (folder.isDirectory() && folder.getName().contains(id))
		// imageDir = folder;
		// logger.debug("found export folder " + imageDir + " in " + jpegDir);
		// }
		// } else {
		// logger.debug("found export folder " + imageDir + " in " + tiffDir);
		// }
		// }

		// get temp dir
		File tempDir = new File(importFolder, getProcessTitle().replace(".xml", ""));
		File tempImageDir = new File(tempDir, "images");
		File tempTiffDir = new File(tempImageDir, getProcessTitle().replace(".xml", "") + "_tif");
		File tempOrigDir = new File(tempImageDir, "orig_" + getProcessTitle().replace(".xml", "") + "_tif");
		tempTiffDir.mkdirs();
		
		// check if we have an image Dir now
		for (File imageDir : imageDirs) {

			if (imageDir == null || imageDir.listFiles() == null || imageDir.listFiles().length == 0) {
				logger.warn("Empty image dir: " + imageDir.getAbsolutePath() + ". Ignoring");
				continue;
			}

			// parse all image Files and write them into new Files in the import
			// directory
			List<File> images = Arrays.asList(imageDir.listFiles(ImageFilter));
			for (File imageFile : images) {
				try {
					String filename = imageFile.getName();
					copyFile(imageFile, new File(tempTiffDir, filename));
					if (deleteOriginalImages) {
						imageFile.delete();
					}
				} catch (Exception e) {
					logger.error(e.getMessage(), e);
				}
			}
		}
	}

	private void copyFile(File source, File dest) throws IOException {
		InputStream inStream = new FileInputStream(source);
		BufferedInputStream bis = new BufferedInputStream(inStream);
		FileOutputStream fos = new FileOutputStream(dest);
		byte[] bytes = new byte[8192];
		int count = bis.read(bytes);
		while (count != -1 && count <= 8192) {
			fos.write(bytes, 0, count);
			count = bis.read(bytes);
		}
		if (count != -1) {
			fos.write(bytes, 0, count);
		}
		fos.close();
		bis.close();
	}

	/**
	 * 
	 * makes the physical and logical structMap of doc compatible with goobi
	 * 
	 * @param doc
	 * @param modsDoc
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private Document replaceStructData(Document doc, Document modsDoc) {

		Element physStruct = null, logStruct = null;
		List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);

		// set filegroup use to local
		Element fileSec = doc.getRootElement().getChild("fileSec", mets);
		if (fileSec != null) {
			Element fileGrp = fileSec.getChild("fileGrp", mets);
			fileGrp.setAttribute("USE", "LOCAL");
		}

		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL"))
				physStruct = element;
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL"))
				logStruct = element;
		}

		// get logical structMap of modsDoc
		Element modsLogStruct = null;
		List<Element> modsChildren = modsDoc.getRootElement().getChildren();
		for (Element element : modsChildren) {
			if (element.getName().contentEquals(logStruct.getName()) && element.getAttributeValue("TYPE").contentEquals("LOGICAL")) {
				modsLogStruct = element;
				break;
			}
		}

		// set type of logical root
		Element logRoot = null;
		for (Object obj : logStruct.getChildren("div", mets)) {
			if (obj instanceof Element)
				logRoot = (Element) obj;
			else
				break;

			if (isSeriesVolume)
				logRoot.setAttribute("TYPE", getLogicalSubType(modsDoc));
			else
				logRoot.setAttribute("TYPE", getLogicalType(modsDoc));
		}

		// set type of physical root
		Element physRoot = null;
		for (Object obj : physStruct.getChildren("div", mets)) {
			if (obj instanceof Element) {
				physRoot = (Element) obj;
				break;
			} else {
				continue;
			}
		}
		physRoot.setAttribute("TYPE", getPhysicalType(modsDoc));

		// integrate logical structMaps
		if (isSeriesVolume) {
			List<Content> logicalChildren = logStruct.removeContent();
			logStruct.addContent(modsLogStruct.removeContent());
			Element seriesElement = logStruct.getChild("div", mets);
			seriesElement.removeChildren("div", mets);
			seriesElement.addContent(logicalChildren);
		}

		// make physDocStrct comply to BoundBook->page
		List<Element> volumes = physRoot.getChildren();
		List<Element> pages = new ArrayList<Element>();
		int noVolumes = 0;

		// get all pages in the physical DocStruct
		for (Element volume : volumes) {
			noVolumes++;
			pages.addAll(getPhysicalPages(volume));
		}

		// remove all children of the physical root (BoundBook)
		physRoot.removeChildren("div", mets);

		// add all pages to the physical root (BoundBook)
		for (Element element : pages) {
			physRoot.addContent((Element) element.clone());
		}

		// rename PAGE->page
		Iterator<Content> descendant = physRoot.getDescendants();
		while (descendant.hasNext()) {
			Element ele = null;
			Object obj = descendant.next();
			if (obj instanceof Element) {
				ele = (Element) obj;
				String value = ele.getAttributeValue("TYPE");
				if (value != null && value.contentEquals("PAGE")) {
					// Exchange values of LABEL and ORDERLABEL
					String label = ele.getAttributeValue("LABEL");
					String orderLabel = ele.getAttributeValue("ORDERLABEL");
					ele.setAttribute("LABEL", orderLabel);
					ele.setAttribute("ORDERLABEL", label);

					ele.setAttribute("TYPE", "page");
				}
			}
		}

		return doc;
	}

	private ArrayList<Element> getPhysicalPages(Element parent) {

		ArrayList<Element> pages = new ArrayList<Element>();

		List children = parent.getChildren();
		for (Object object : children) {
			if (object instanceof Element) {
				Element child = (Element) object;
				if (child.getAttributeValue("TYPE").toLowerCase().contentEquals("page")) {
					// child is a page
					pages.add(child);
				} else {
					pages.addAll(getPhysicalPages(child));
				}
			}
		}

		return pages;
	}

	/**
	 * Puts the logical StructData before physical StructData in the document structure of doc
	 * 
	 * @param doc
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private Document exchangeStructData(Document doc) {

		List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);
		Element structLink = doc.getRootElement().getChild("structLink", mets);
		Element physStruct = null, logStruct = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL"))
				physStruct = element;
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL"))
				logStruct = element;
		}

		physStruct.detach();
		logStruct.detach();
		structLink.detach();

		doc.getRootElement().addContent(logStruct);
		doc.getRootElement().addContent(physStruct);
		doc.getRootElement().addContent(structLink);

		return doc;
	}

	/**
	 * 
	 * replaces the xmlData (actually the content of dmdSec) of doc with that of marcDoc
	 * 
	 * @param doc
	 * @param marcDoc
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private Document replaceXmlData(Document doc, Document marcDoc) {

		String dmdID = " ";

		// get old and new Dmd sections
		List<Element> newDmdSecs = marcDoc.getRootElement().getChildren("dmdSec", mets);

		// remove all Children of rootElement and save them as list
		List<Content> objects = doc.getRootElement().removeContent();
		List<Element> elements = new ArrayList<Element>();
		for (Content content : objects) {
			if (content instanceof Element) {
				elements.add((Element) content);
				logger.debug("adding Element to new root children list");
			}
		}

		// reattach all children of root, except "dmdSec", which is replaced by the two new sections
		for (Element element : elements) {
			if (element.getName().contentEquals("dmdSec")) {
				// get child of first dmdSec
				Element dmdChild = (Element) newDmdSecs.get(0).getChild("mdWrap", mets).clone();
				element.setContent(dmdChild);
				doc.getRootElement().addContent(element);

				if (newDmdSecs.size() > 1) // check if we have indeed two dmdSecs
				{
					Element newDmdSec2 = (Element) newDmdSecs.get(1).clone();
					dmdID = newDmdSec2.getAttributeValue("ID");
					doc.getRootElement().addContent(newDmdSec2);
				}
			} else {
				// all other elements, just reattach
				doc.getRootElement().addContent(element);
				// and set imagepath id for first child in physStructMap
				if (element.getName().contentEquals("structMap") && element.getAttributeValue("TYPE").contentEquals("PHYSICAL")) {
					logger.debug("adding reference DMDID=" + dmdID + " to physical structMap");
					Element book = element.getChild("div", mets);
					book.setAttribute("DMDID", dmdID);
				}
			}
		}
		return doc;
	}

	/**
	 * Unzip a zip archive and write results into Array of Strings
	 * 
	 * @param source
	 * @return
	 */
	private HashMap<String, byte[]> unzipFile(File source) {
		ArrayList<String> stringList = new ArrayList<String>();
		ArrayList<String> filenames = new ArrayList<String>();
		HashMap<String, byte[]> contentMap = new HashMap<String, byte[]>();

		try {
			ZipInputStream in = new ZipInputStream(new BufferedInputStream(new FileInputStream(source)));
			ZipEntry entry;
			while ((entry = in.getNextEntry()) != null) {
				filenames.add(entry.getName());
				logger.debug("Unzipping file " + entry.getName() + " from archive " + source.getName());
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				BufferedOutputStream out = new BufferedOutputStream(baos);
				int size;
				byte[] buffer = new byte[2048];
				while ((size = in.read(buffer, 0, buffer.length)) != -1) {
					out.write(buffer, 0, size);
				}

				if (entry != null)
					in.closeEntry();
				if (out != null) {
					out.close();
				}
				if (baos != null) {
					baos.close();
				}
				contentMap.put(entry.getName(), baos.toByteArray());

				// BufferedReader br = new BufferedReader(new InputStreamReader(in));
				// StringBuffer sb = new StringBuffer();
				// String line;
				// while ((line = br.readLine()) != null) {
				// sb.append(line)/*.append("\n")*/;
				// }
				// stringList.add(sb.toString());
				// contentMap.put(entry.getName(), sb.toString());
			}
		} catch (IOException e) {
			logger.error(e.toString(), e);
		}

		return contentMap;
	}

	private HashMap<String, String> unzipStream(InputStream iStream) {
		ArrayList<String> stringList = new ArrayList<String>();
		ArrayList<String> filenames = new ArrayList<String>();
		HashMap<String, String> contentMap = new HashMap<String, String>();

		try {
			ZipInputStream in = new ZipInputStream(new BufferedInputStream(iStream));
			ZipEntry entry;
			while ((entry = in.getNextEntry()) != null) {
				filenames.add(entry.getName());
				BufferedReader br = new BufferedReader(new InputStreamReader(in));
				StringBuffer sb = new StringBuffer();
				String line;
				while ((line = br.readLine()) != null) {
					sb.append(line).append("\n");
				}
				stringList.add(sb.toString());
				contentMap.put(entry.getName(), sb.toString());
			}
		} catch (IOException e) {
			logger.error(e.toString(), e);
		}

		return contentMap;
	}

	/**
	 * Sets the namespace of all Elements within Element root to Namespace ns
	 * 
	 * @param root
	 * @param ns
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static Element setNamespaceRecursive(Element root, Namespace ns) {
		List<Element> current = new ArrayList<Element>();
		current.add(root);
		do {
			List<Element> children = new ArrayList<Element>();
			for (Element element : current) {
				element.setNamespace(ns);
				children.addAll(element.getChildren());
			}
			current = children;
		} while (!current.isEmpty());

		return root;
	}

	private Document getMarcModsLoss(Document marcDoc, Document modsDoc) {

		Element record = marcDoc.getRootElement();
		if (record == null) {
			return null;
		}

		Document missingElementsDoc = new Document(new Element("Lost-in-MarcMods-Conversion"));
		String modsString = CommonUtils.getStringFromDocument(modsDoc, encoding);
		// modsString = modsString.replaceAll("\"", "");

		Iterator<Content> descendant = record.getDescendants();
		while (descendant.hasNext()) {
			Element ele = null;
			Object obj = descendant.next();
			if (obj instanceof Element) {
				ele = (Element) obj;
				String marcContent = ele.getText();
				if (marcContent != null && !marcContent.isEmpty()) {
					try {
						CharSequence cs = marcContent.trim().subSequence(0, marcContent.trim().length() - 1);
						marcContent = cs.toString().trim();
						if (modsString.contains(marcContent)) {
							// marc field is contained in the mods doc
						} else {
							Element parentElement = ele.getParentElement();
							if (parentElement != null && parentElement != record) {
								// The element has a parent that is not the root element, which we should log as well
								Element parentClone = (Element) parentElement.clone();
								parentClone.removeContent();
								missingElementsDoc.getRootElement().addContent(parentClone);
								parentClone.addContent((Element) ele.clone());
							} else {
								missingElementsDoc.getRootElement().addContent((Element) ele.clone());
							}
						}
					} catch (IndexOutOfBoundsException e) {
						continue;
					}
				}

			}
		}
		return missingElementsDoc;
	}

	public static void main(String[] args) throws PreferencesException, WriteException {
		CSICMixedImport converter = new CSICMixedImport();
		converter.prefs = new Prefs();

		try {
			converter.prefs.loadPrefs("resources/rulesetCSIC.xml");
		} catch (PreferencesException e) {
			logger.error(e.getMessage(), e);
		}

		converter.setImportFolder("output/");
		List<Record> records = new ArrayList<Record>();
		if (!converter.exportFolder.isDirectory()) {
			logger.warn("No export directory found. Aborting");
			return;
		}

		for (File file : converter.exportFolder.listFiles(XmlFilter)) {

			// converter.createFileformat(file);
			converter.setFile(file);
			records.addAll(converter.generateRecordsFromFile());
		}

		List<ImportObject> results = converter.generateFiles(records);

		for (ImportObject record : results) {
			System.out.println(record.getProcessTitle() + " \t \t " + record.getImportReturnValue());
		}
	}

	// private Document getModsMetsLoss(Document modsDoc, Document metsDoc) {
	//
	// }

	public static FilenameFilter ImageFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			// tif
			if (name.endsWith("tif") || name.endsWith("TIF")) {
				validImage = true;
			}

			// jpg
			if (name.endsWith("jpg") || name.endsWith("JPG") || name.endsWith("jpeg") || name.endsWith("JPEG")) {
				validImage = true;
			}

			return validImage;
		}
	};

	public static FilenameFilter XmlFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("xml") || name.endsWith("XML")) {
				validImage = true;
			}

			return validImage;
		}
	};

	public static FilenameFilter zipFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("zip") || name.endsWith("ZIP")) {
				validImage = true;
			}

			return validImage;
		}
	};

	// Filters for file searches
	public static FileFilter DirFilter = new FileFilter() {
		public boolean accept(File file) {
			return file.isDirectory();
		}
	};

	@Override
	public List<Record> generateRecordsFromFilenames(List<String> filenames) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<ImportProperty> getProperties() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<String> getAllFilenames() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void deleteFiles(List<String> selectedFilenames) {
		// TODO Auto-generated method stub

	}

	@Override
	public List<DocstructElement> getCurrentDocStructs() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String deleteDocstruct() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String addDocstruct() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<String> getPossibleDocstructs() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public DocstructElement getDocstruct() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setDocstruct(DocstructElement dse) {
		// TODO Auto-generated method stub

	}
}
